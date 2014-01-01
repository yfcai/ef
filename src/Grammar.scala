trait Lexer {
  case class Problem(token: Token, message: String)
      extends Exception(
    s"""|${token.fileLine}
        |${token.residentLines(3)}
        |$message
        |""".stripMargin)

  case class Token(body: String, location: Int, paragraph: Paragraph) {
    override def toString = s"$location:$body"
    def file: String = paragraph.file
    def line: Int = paragraph.line +
      (paragraph.body.substring(0, location) count (_ == '\n'))
    def fileLine: String = Token.fileLine(file, line)

    def isLeftParen  = body == "("
    def isRightParen = body == ")"

    def residentLines(n: Int): String = {
      assert(paragraph.body(location) != '\n')
      def loop(n: Int, start: Int): Int =
        if (start < 0)
          0
        else if (n <= 1)
          paragraph.body.lastIndexOf('\n', start) + 1
        else
          loop(n - 1, paragraph.body.lastIndexOf('\n', start) - 1)
      val start: Int = loop(n, location)
      val end: Int = paragraph.body.indexOf('\n', location)
      val theLine =
        (paragraph.body substring (start,
          if (end < 0) paragraph.body.length else end)).lines.dropWhile(
          _.find(! _.isSpace) == None
        ) mkString "\n"
      val relativeLocation = location - loop(1, location)
      s"$theLine\n${Array.fill(relativeLocation)(' ').mkString}^"
    }
  }

  object Token {
    def fileLine(file: String, line: Int): String =
      s"${file substring (1 + (file lastIndexOf '/'))}:$line"
  }

  // keywords (always a token by itself):
  def keywords: Set[String]

  def tokenize(p: Paragraph): Seq[Token] = new TokenIterator(p).toSeq

  def tokenize(s: String): Seq[Token] = tokenize(Paragraph(s))

  class TokenIterator(
    paragraph: Paragraph,
    var location: Int = 0
  ) extends Iterator[Token] {
    def hasNext: Boolean = {
      tryToFindNextToken()
      ! nextTokenNotFound
    }

    def next: Token = {
      tryToFindNextToken()
      if (nextTokenNotFound) sys error s"next of $this"
      val result = nextToken
      resetNextToken
      result
    }

    def remains: String = paragraph.body substring location

    var nextToken: Token = null

    def nextTokenNotFound = nextToken == null

    def resetNextToken() = nextToken = null

    def tryToFindNextToken() {
      // we found a next token from a previous run
      if (nextToken != null) return ()
      // find first nonspace
      val from = remains indexWhere (! _.isSpace)
      // we ran out of nonspaces, giving up
      if (from < 0) return ()
      tryKeyword(from) map {
        case x => { foundNextToken(from, x) ; return }
      }
      tryIdentifier(from) map {
        case x => { foundNextToken(from, x) ; return }
      }
      // ran outta tokens!
      location = paragraph.body.length
    }

    def tryIdentifier(from: Int): Option[String] = {
      var end = firstDelimiter(from)
      Some(remains substring (from, end))
    }

    def tryKeyword(from: Int): Option[String] =
      keywords findFirst { s =>
        if (remains.startsWith(s, from))
          Some(s)
        else
          None
      }

    // a delimiter is either space or the first character of a keyword.
    def firstDelimiter(from: Int): Int = {
      val space = positivize(remains indexWhere (_.isSpace, from))
      val keychar = keywords.map({
        keyword => positivize(remains indexOf (keyword, from))
      }).min
      Math.min(space, keychar)
    }

    // convert -1 to remains.length
    def positivize(i: Int) = if (i < 0) remains.length else i

    def foundNextToken(from: Int, x: String) {
      nextToken = Token(x, location + from, paragraph)
      location += from + x.length
    }
  }

  implicit class UsefulCharOperations(c: Char) {
    import java.lang.Character
    def isSpace = Character.isWhitespace(c)
  }

  implicit class UsefulStringOperations(s: String) {
    // a line comment is either empty, consists entirely of
    // spaces, or has '.' as first nonspace, provided that it's
    // not a paragraph comment. A paragraph comment consumes the
    // whole paragraph along with all intervening line comments.
    //
    // line comments are far removed from paragraph comments
    // have no idea how to deal with line comments modularly
    def isLineComment: Boolean =
      ! s.isParagraphComment &&
      (s.isEmpty || s.firstNonSpace == '.' || s.map(_.isSpace).min)

    def isParagraphComment: Boolean = s matches """\.\s*rant(|\s.*)"""

    def firstNonSpace: Char = {
      val i = s indexWhere (! _.isSpace)
      if (i < 0) ' ' else s(i)
    }
  }

  implicit class FindFirstInLine[T](seq: Iterable[T]) {
    def findFirst[R](f: T => Option[R]): Option[R] = {
      var z: Option[R] = None
      seq.find(x => f(x) match {
        case None => false
        case Some(result) => { z = Some(result) ; true }
      })
      z
    }
  }

  /** Chop file into paragraphs. A paragraph is a continguous set
    * of lines such that the first line starts with a nonspace and
    * the other lines start with a space.
    */
  case class Paragraph(file: String, line: Int, body: String)

  object Paragraph {
    val defaultFile = "#LINE"
    val firstLine = 1
    def apply(s: String): Paragraph = Paragraph(defaultFile, firstLine, s)
  }

  object Paragraphs {
    def apply(s: String): Paragraphs =
      Paragraphs(Paragraph.defaultFile, s.lines)
    def fromFile(file: String): Paragraphs =
      Paragraphs(file, scala.io.Source.fromFile(file).getLines)
  }

  case class Paragraphs(file: String, _lines: Iterator[String])
  extends Iterator[Paragraph] {
    def hasNext: Boolean = ! lines.isEmpty
    def next: Paragraph = {
      if (lines.isEmpty) sys error s"next of $this"
      var startOfNextParagraph =
        lines indexWhere (
          x => x.isParagraphComment || !x.isLineComment && !x.head.isSpace,
          1)
      if (startOfNextParagraph < 0) startOfNextParagraph = lines.length
      val (thisParagraph, theRest) = lines splitAt startOfNextParagraph
      val thisLineNumber = nextLineNumber
      lines = theRest
      nextLineNumber += startOfNextParagraph
      Paragraph(
        file,
        thisLineNumber,
        (thisParagraph filterNot (_.isLineComment)) mkString "\n"
      )
    }

    var lines: Stream[String] = null
    var nextLineNumber = Paragraph.firstLine

    {
      val (int, stream) = removeEmptyLines(_lines.toStream)
      lines = stream
      nextLineNumber += int
    }

    def removeEmptyLines(lines: Stream[String]): (Int, Stream[String]) = {
      var result = lines
      var emptyLines = 0
      while(! result.isEmpty && result.head.isLineComment) {
        result = result.tail
        emptyLines += 1
      }
      (emptyLines, result)
    }
  }
}

/** ProtoAST, tree obtained by considering parentheses alone */
trait ProtoAST extends Lexer with Trees {
  // variadic tree
  case object TokenAST extends LeafTag {
    def genus = ProtoAST
    final val man = manifest[Token]
  }

  case object ProtoAST extends UnclassifiedTag {
    // tree
    def apply(string: String): Seq[Tree] = apply(tokenize(string))

    def apply(toks: Seq[Token]): Seq[Tree] = {
      def theatre(candidate: Seq[Tree], next: Seq[Token]) =
        if (next.isEmpty)
          candidate
        else
          throw Problem(next.head, "unmatched right parenthesis")
      if (! toks.isEmpty && toks.head.isLeftParen) {
        val (me, next) = vertical(toks)
        if (next.isEmpty)
          Seq(me)
        else {
          val (children, rest) = horizontal(next)
          theatre(me +: children, rest)
        }
      }
      else {
        val (children, next) = horizontal(toks)
        theatre(children, next)
      }
    }

    // tree (tree) tree (tree) tree
    def horizontal(toks: Seq[Token]): (List[Tree], Seq[Token]) =
      if (toks.isEmpty)
        (Nil, Nil)
      else if (toks.head.isLeftParen) {
        val (next, rest) = vertical(toks)
        val (others, residual) = horizontal(rest)
        (next :: others, residual)
      }
      else if (toks.head.isRightParen)
        (Nil, toks)
      else {
        val (others, residual) = horizontal(toks.tail)
        (∙(TokenAST, toks.head) :: others, residual)
      }

    // ( ( ( ( ( tree ) ) ) ) )
    // precondition: toks0.head.isLeftParen
    def vertical(toks0: Seq[Token]): (Tree, Seq[Token]) = {
      // switch the following check off for performance
      require(! toks0.isEmpty && toks0.head.isLeftParen)
      def emptyProblem =
        throw Problem(toks0.last, "expect right parenthesis after this")
      def mkProtoAST(children: Seq[Tree]) =
        ⊹(ProtoAST, children: _*)
      def theatre(next: Tree, rest: Seq[Token]) =
        if (rest.isEmpty)
          emptyProblem
        else if (rest.head.isRightParen)
          (next, rest.tail)
        else
          throw Problem(rest.head, "expect right parenthesis here")
      val toks = toks0.tail
      if (toks.isEmpty)
        emptyProblem
      else if (toks.head.isLeftParen) {
        val (next, rest) = vertical(toks)
        if (rest.isEmpty || rest.head.isRightParen)
          theatre(next, rest)
        else {
          val (children, realRest) = horizontal(rest)
          theatre(mkProtoAST(next +: children), realRest)
        }
      }
      else if (toks.take(2).length == 2 &&
               ! toks(0).isRightParen &&
                 toks(1).isRightParen)
        (∙(TokenAST, toks.head), toks.drop(2))
      else {
        val (children, rest) = horizontal(toks)
        theatre(mkProtoAST(children), rest)
      }
    }
  }
}

trait Fixities extends ProtoAST {
  trait Fixity {
    type Item = Tree
    type Items = Seq[Tree]
    type ItemGroups = Seq[Seq[Tree]]

    def splits(items: Items): Iterator[ItemGroups]

    // helper for dealing with tokens
    def hasBody(t: Tree, op: String): Boolean = t match {
      case ∙(TokenAST, tok: Token) => tok.body == op
      case _ => false
    }
  }

  case object AllItemsTogether extends Fixity {
    def splits(items: Items) = Iterator(Seq(items))
  }

  trait Juxtaposed extends Fixity

  case object IndividualItems extends Juxtaposed {
    def splits(items: Items): Iterator[ItemGroups] =
      Iterator(items.map(x => Seq(x)))
  }

  case object Juxtaposition extends Juxtaposed {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.length >= 2)
        Iterator(Seq(items.init, Seq(items.last)))
      else
        Iterator.empty
  }

  case class Prefix(ops: String*) extends Fixity {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.isEmpty)
        Iterator.empty
      else if (hasBody(items.head, ops.head))
        Infixr(ops.tail: _*) splits items.tail
      else
        Iterator.empty
  }

  case class Postfix(ops: String*) extends Fixity {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.isEmpty)
        Iterator.empty
      else if (hasBody(items.last, ops.last))
        Infixl(ops.init: _*) splits items.init
      else
        Iterator.empty
  }

  case class LoneToken(forbidden: Set[String]) extends Fixity {
    def splits(items: Items) = items match {
      case Seq(∙(TokenAST, token: Token))
          if ! (forbidden contains token.body) =>
        Iterator(Seq(items))
      case _ =>
        Iterator.empty
    }
  }

  case class Infixr(ops: String*) extends Infix {
    def cloneMyself = Infixr.apply
    def initialHeadPosition(items: Items) = 0
    def nextHeadPosition(items: Items, headPosition: Int): Int =
      items.indexWhere(x => hasBody(x, ops.head), headPosition + 1)
  }

  case class Infixl(ops: String*) extends Infix {
    def cloneMyself = Infixl.apply
    def initialHeadPosition(items: Items) = items.length - 1
    def nextHeadPosition(items: Items, headPosition: Int): Int =
      items.lastIndexWhere(x => hasBody(x, ops.head), headPosition - 1)
  }

  trait Infix extends Fixity {
    def ops: Seq[String]
    def cloneMyself: Seq[String] => Infix
    def initialHeadPosition(items: Items): Int
    def nextHeadPosition(items: Items, headPosition: Int): Int

    def splits(items: Items): Iterator[ItemGroups] =
      if (items.isEmpty)
        Iterator.empty
      else if (ops.isEmpty)
        Iterator(Seq(items))
      else
        InfixIterator(items)

    case class InfixIterator(items: Items) extends Iterator[ItemGroups] {
      var headPosition = initialHeadPosition(items)

      val suffix = cloneMyself(ops.tail)

      var suffixIterator: Iterator[ItemGroups] = Iterator.empty

      var nextCandidate: ItemGroups = null

      var thisPortion: Items = null

      // precondition: suffixIterator.hasNext && thisPortion != null
      def resultFromSuffix(): ItemGroups =
        thisPortion +: suffixIterator.next

      def tryToFindNextCandidate() {
        // next candidate is there; don't have to look again
        if (nextCandidate != null) return ()
        // can produce next candidate from suffix iterator
        if (suffixIterator.hasNext) {
          nextCandidate = resultFromSuffix()
          return ()
        }
        // this iterator is already exhausted; do nothing
        if (headPosition < 0) return ()
        // find the next possible head
        headPosition = nextHeadPosition(items, headPosition)
        // this iterator becomes exhausted; do nothing
        if (headPosition < 0) return ()
        // found next head. time to construct suffixIterator.
        val (beforeHead, headAndMore) = items splitAt headPosition
        thisPortion    = beforeHead
        suffixIterator = suffix splits headAndMore.tail
        if (suffixIterator.hasNext)
          nextCandidate = resultFromSuffix()
      }

      def nextCandidateNotFound = nextCandidate == null

      def resetNextCandidate() { nextCandidate = null }

      def hasNext: Boolean = {
        tryToFindNextCandidate()
        ! nextCandidateNotFound
      }

      def next: ItemGroups = {
        tryToFindNextCandidate()
        if (nextCandidateNotFound) sys error s"next of empty $this"
        val result = nextCandidate
        resetNextCandidate()
        result
      }
    }
  }
}


trait Operators extends Fixities {
  trait Operator extends Tag {
    def fixity: Fixity
    def toTryNext: Seq[Any] => Seq[Seq[Operator]]

    /** @param children
      * is the sequence of proto-ASTs allotted to this node if it
      * is a leaf, and is the sequence of children if it is not.
      */
    def cons(children: Seq[Tree]): Tree

    // extension point to introduce fast failures
    def precondition(items: Seq[Tree]): Boolean = true

    def parse(string: String): Option[Tree] = parse(ProtoAST(string))

    def parse(items: Seq[Tree]): Option[Tree] = {
      if (precondition(items) == false)
        return None

      val splits = fixity splits items
      val tryNext = toTryNext(items)
      if (tryNext.isEmpty) {
        // nothing to try next, produce a leaf
        if (splits.hasNext) {
          val x = splits.next match {
            case Seq(x) => x
            case _ =>
              sys error s"leaf operator with nonunary fixity: $this"
          }
          Some(cons(x))
        }
        else
          None
      }
      else {
        // got stuff to try next, produce a branch.
        while(splits.hasNext) {
         val split = splits.next
         // assertion to locate buggy operators
         if(split.length != tryNext.length)
           sys error s"operator $this declares arity ${
             split.length
           } but has ${tryNext.length} children"
          val maybeChildren: Option[List[Tree]] =
            (tryNext, split).zipped.foldRight(
              Some(Nil): Option[List[Tree]]
            ) {
              case ((_, _), None) => None
              case ((parsersToTry, items), Some(bros)) =>
                parsersToTry findFirst (_ parse items) map (_ :: bros)
            }
          // if a feasible split is found, do not try other,
          // less preferable, splits.
          maybeChildren match {
            case None => ()
            case Some(children) => return Some(cons(children))
          }
        }
        // I can't parse it
        None
      }
    }

    override def unparse(t: Tree): String = t match {
      case ⊹(operator: Operator, children @ _*) =>
        val tokens = children map (x => x.tag unparse x)
        val subops = operator toTryNext tokens
        val parens = ((children map (_.tag), tokens).zipped, subops).zipped.
          map({
            case ((childOp, child), subOps) =>
              if (subOps contains childOp) child
              else                     s"($child)"
          }).toSeq
        pack(operator.fixity match {
          case _: Juxtaposed =>
            parens
          case p: Prefix     =>
            prefixLike(p.ops, parens)
          case p: Postfix    =>
            postfixLike(p.ops, parens)
          case i: Infix      =>
            parens.head +: prefixLike(i.ops, parens.tail)
        })
      case leaf @ ∙(op: LeafOperator, _) =>
        op unparseLeaf leaf
      case _ =>
        sys error s"dunno how to unparse:\n${t.print}"
    }

    // duplicates partial info in keyword. how to merge?
    private
    val leftParens  = Set('{', '[', 'λ', 'Λ', '∀', '∃')
    private
    val rightParens = Set('}', ']', '.')

    private[this]
    def pack(tokens: Seq[String]): String =
      (tokens.head +: ((tokens, tokens.tail).zipped.flatMap {
        case (before, after)
            if before.length == 1 && (leftParens contains before.head)
            || after .length == 1 && (rightParens contains after.head) =>
          List(after)
        case (_, after) =>
          List(" ", after)
      })).mkString

    private[this]
    def prefixLike(ops: Seq[String], children: Seq[String]): Seq[String] =
      (ops, children).zipped flatMap {
        case (op, child) => List(op, child)
      }

    private[this]
    def postfixLike(ops: Seq[String], children: Seq[String]): Seq[String] =
      prefixLike(children, ops)
  }

  trait LeafOperator extends Operator with LeafTag {
    def fixity: Fixity
    def genus: Genus
    def man: Manifest[_]

    def unparseLeaf(leaf: ∙[_]): String

    override def toTryNext = _ => Seq.empty[Seq[Operator]]
  }
}

/*
trait ExpressionGrammar extends Grammar {
  type Domain = String

  // keywords (always a token by itself):
  val keywords = "( ) [ ] { } ∀ ∃ Λ λ .".words

  // things that can't be a name:
  lazy val forbidden = "( ) .".words

  implicit class SplitStringIntoWords(s: String) {
    def words: Set[String] = Set(s split " ": _*)
  }

  case object Atomic extends Operator(LoneToken(forbidden), Nil)

  case object TypeParenthetic extends Operator(
    Enclosing("(", ")"),
    Seq(typeOps)
  )

  case object TermParenthetic extends Operator(
    Enclosing("(", ")"),
    Seq(termOps)
  )

  // ... super constructor cannot be passed a self reference
  // unless parameter is declared by-name ... (facepalm)
  def functorApplicationSelfReference = FunctorApplication

  case object FunctorApplication extends Operator(
    Juxtaposition,
    Seq(downFrom(functorApplicationSelfReference, typeOps),
        downFrom(TypeParenthetic, typeOps))
  )

  case object TermApplication extends Operator(
    Juxtaposition,
    Seq(downFrom(TypeInstantiation, termOps),
        downFrom(TermParenthetic  , termOps))
  )

  case object TypeAmnesia extends Operator(
    Infixl(":"),
    Seq(downFrom(TypeInstantiation, termOps),
        typeOps)
  )

  def typeInstantiationSelfReference  = TypeInstantiation

  case object TypeInstantiation extends Operator(
    Postfix("[", "]"),
    Seq(downFrom(typeInstantiationSelfReference, termOps), typeOps)
  )

  def functionArrowSelfReference = FunctionArrow

  case object FunctionArrow extends Operator(
    Infixr("→"),
    // allowing all type expressions to appear on rhs of arrow
    Seq(downBelow(functionArrowSelfReference, typeOps), typeOps)
  )

  def typeParameterListSelfReference = TypeParameterList

  case object TypeParameterList extends Operator(
    IndividualTokens,
    _ map (_ => Seq(Atomic))
  )

  case object ExistentialQuantification extends Operator(
    Prefix("∃", "."),
    Seq(Seq(TypeParameterList), typeOps)
  )

  case object UniversalQuantification extends Operator(
    Prefix("∀", "."),
    Seq(Seq(TypeParameterList), typeOps)
  )

  case object TypeAbstraction extends Operator(
    Prefix("Λ", "."),
    Seq(Seq(TypeParameterList), termOps)
  )

  case object TermAbstraction extends Operator(
    Prefix("λ", ":", "."),
    Seq(Seq(Atomic), typeOps, termOps)
  )

  case object LetBinding extends Operator(
    Prefix("let", "=", "in"),
    Seq(Seq(Atomic), termOps, termOps)
  )

  val typeOps: List[Operator] =
    List(
      UniversalQuantification   ,
      ExistentialQuantification ,
      FunctionArrow             ,
      FunctorApplication        ,
      TypeParenthetic           ,
      Atomic                    )

  val termOps: List[Operator] =
    List(
      LetBinding        ,
      TermAbstraction   ,
      TypeAbstraction   ,
      TypeAmnesia       ,
      TypeInstantiation ,
      TermApplication   ,
      TermParenthetic   ,
      Atomic            )

  def downFrom(x: Operator, ops: List[Operator]): List[Operator] =
    ops match {
      case y :: tail if x == y => ops
      case _ :: tail => downFrom(x, tail)
      case Nil => sys error s"$x not found in $ops"
    }

  def downBelow(x: Operator, ops: List[Operator]): List[Operator] =
    downFrom(x, ops) match {
      case Nil | _ :: Nil => sys error s"nothing below $x in $ops"
      case x :: tail => tail
    }
}

// parse file, produce AST
trait ParagraphGrammar extends ExpressionGrammar with Paragraphs {
  class DummyOperator(parsersToTry: Seq[Operator])
  extends Operator(AllTokensTogether, Seq(parsersToTry)) {
    override def parse(tokens: Tokens): Option[AST] =
      super.parse(tokens) map {
        case Branch(_, List(realAST)) => realAST
      }
  }

  class DefinitionOperator(
    definingSymbol: String, rhs: Operator
  ) extends Operator (
    Infixr(definingSymbol),
    Seq(Seq(Atomic), Seq(rhs))
  ) {
    override def precondition(tokens: Tokens) =
      (tokens isDefinedAt 1) && tokens(1) == definingSymbol
  }

  case object TypeExpr      extends DummyOperator(typeOps)
  case object TermExpr      extends DummyOperator(termOps)
  case object ParagraphExpr extends DummyOperator(paragraphOps) {
    def fromFileWithLines(path: String): Iterator[(AST, Int)] =
      (Paragraphs fromFile path) map {
        p => (fromParagraph(path.split("/").last)(p), p.line)
      }

    def fromFile(path: String): Iterator[AST] =
      (Paragraphs fromFile path) map fromParagraph(path.split("/").last)

    def withLines(string: String): Iterator[(AST, Int)] =
      Paragraphs(string) map {
        p => (fromParagraph("#LINE")(p), p.line)
      }

    def apply(string: String): Iterator[AST] =
      Paragraphs(string) map fromParagraph("#LINE")

    def fromParagraph(path: String)(paragraph: Paragraph): AST =
      parse(paragraph.body) match {
        case None =>
          sys error s"\n$path:${paragraph.line}   PARSE ERROR\n"
        case Some(ast) =>
          ast
      }
  }

  case object ParagraphComment
  extends Operator(AllTokensTogether, Nil) {
    override def precondition(tokens: Tokens) =
      tokens.startsWith(Seq(".", "rant"))
  }

  case object TypeSynonym extends Operator (
    Prefix("type", "="),
    Seq(Seq(TypeParameterList), Seq(TypeExpr))
  )

  case object TypeSignature
  extends DefinitionOperator(":", TypeExpr)

  case object TermDefinition
  extends DefinitionOperator("=", TermExpr)

  // can't set TermParameterList = TypeParameterList
  // because we want to make tag.toString distinct
  // so as not to confuse humans
  case object TermParameterList extends Operator(
    IndividualTokens,
    _ map (_ => Seq(Atomic))
  )

  // we'd like to try TypedFUnctionDefinition last
  // because it fails more slowly than others
  case object TypedFUnctionDefinition extends Operator (
    Infixr("="),
    Seq(Seq(TermParameterList), Seq(TermExpr))
  ) {
    // if "=" comes immediately after a name,
    // then TermDefinition should take care of it.
    override def precondition(tokens: Tokens) =
      (tokens indexOf "=") > 1
  }

  val paragraphOps: List[Operator] =
    List(
      ParagraphComment,
      TypeSynonym,
      TypeSignature,
      TermDefinition,
      TypedFUnctionDefinition)
}

trait ASTConversions extends ExpressionGrammar with Terms {
  implicit class ConversionsFromTypeToOperator(τ: Type) {
    def toAST: AST = τ match {
      case α(binder) =>
        Leaf(Atomic, Seq(Seq(binder.name)))
      case δ(name) =>
        Leaf(Atomic, Seq(Seq(name)))
      case all: ∀ =>
        unnestBinders(all, UniversalQuantification)
      case ex: ∃ =>
        unnestBinders(ex , ExistentialQuantification)
      case σ → τ =>
        Branch(FunctionArrow, List(σ.toAST, τ.toAST))
      case f ₌ τ =>
        Branch(FunctorApplication, List(f.toAST, τ.toAST))
    }
  }

  implicit class ConversionsFromTermToOperator(t: ChurchTerm) {
    def toAST: AST = t.term match {
      case χ(binder) =>
        toAtomic(binder.name)
      case ξ(name) =>
        toAtomic(name)
      case abs @ λ(x, body) =>
        Branch(TermAbstraction,
          List(toAtomic(x.name), (t annotations abs).toAST,
               loop(body)))
      case tabs: Λ =>
        // can't use "unnestBinders" because Λ isn't a binder.
        // maybe we should have some common trait between a binder
        // of bound names and a pseudobinder of free names?
        val (tabses, body) = tabs.detachNestedDoppelgaenger
        Branch(TypeAbstraction,
          List(toParameterList(tabses map (_.alpha.name)),
               loop(body)))

      case ₋(x: λ, xdef) if t.annotations(x) == UnknownType =>
        Branch(LetBinding,
          List(toAtomic(x.name), loop(xdef), loop(x.body)))

      case ₋(f, x) =>
        Branch(TermApplication  , List(loop(f), loop(x)))
      case □(t, τ) =>
        Branch(TypeInstantiation, List(loop(t), τ.toAST))
      case Ξ(t, τ) =>
        Branch(TypeAmnesia      , List(loop(t), τ.toAST))
    }

    private[this]
    def loop(body: Term): AST = ChurchTerm(body, t.annotations).toAST
  }

  private[this] def toAtomic(name: String): AST =
    Leaf(Atomic, Seq(Seq(name)))

  private[this]
  def toParameterList(names: List[String]): AST =
    Branch(TypeParameterList, names map toAtomic)

  private[this]
  def unnestBinders(binder: Type.Binder, binderOp: Operator): AST = {
    val (binders, body) = binder.detachNestedDoppelgaenger
    Branch(binderOp,
      List(toParameterList(binders map (_.name)), body.toAST))
  }

  implicit class ConversionsFromAST(ast: AST) {
    def toProtoChurchTerm: ProtoChurchTerm = ast match {
      case Branch(LetBinding, List(x, xdef, body)) =>
        val t = body.toProtoChurchTerm
        val abs = λ(x.to_ξ)(t.term)
        val ano = UnknownType :: t.annotations
        val dfn = xdef.toProtoChurchTerm
        ProtoChurchTerm(abs ₋ dfn.term, dfn.annotations ++ ano)
      case Branch(TermAbstraction, List(x, xtype, body)) =>
        val t = body.toProtoChurchTerm
        val abs = λ(x.to_ξ)(t.term)
        ProtoChurchTerm(abs, xtype.toType :: t.annotations)
      case Branch(TypeAbstraction,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        val t = body.toProtoChurchTerm
        val parameters = parameterList map (_.to_δ)
        ProtoChurchTerm(Λ(parameters, t.term), t.annotations)
      case Branch(TypeInstantiation, List(term, τ)) =>
        val t = term.toProtoChurchTerm
        ProtoChurchTerm(t.term □ τ.toType, t.annotations)
      case Branch(TypeAmnesia, List(term, τ)) =>
        val t = term.toProtoChurchTerm
        ProtoChurchTerm(t.term Ξ τ.toType, t.annotations)
      case Branch(TermApplication, List(fun, arg)) =>
        val (f, x) = (fun.toProtoChurchTerm, arg.toProtoChurchTerm)
        // annotations are concatenated in reverse preorder
        // (cf. NameBindingLanguage.AST.reverseTraversal)
        ProtoChurchTerm(f.term ₋ x.term, x.annotations ++ f.annotations)
      case Branch(TermParenthetic, List(t)) =>
        t.toProtoChurchTerm
      case x =>
        ProtoChurchTerm(x.to_ξ, Nil)
    }

    def to_ξ: ξ = ast match {
      case Leaf(Atomic, Seq(Seq(name))) =>
        ξ(name)
    }

    def toType: Type = ast match {
      case Branch(UniversalQuantification,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        ∀(parameterList map (_.to_δ), body.toType)
      case Branch(ExistentialQuantification,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        ∃(parameterList map (_.to_δ), body.toType)
      case Branch(FunctionArrow, List(domain, range)) =>
        domain.toType →: range.toType
      case Branch(FunctorApplication, List(functor, arg)) =>
        functor.toType ₌ arg.toType
      case Branch(TypeParenthetic, List(τ)) =>
        τ.toType
      case a =>
        a.to_δ
    }

    def to_δ: δ = ast match {
      case Leaf(Atomic, Seq(Seq(name))) =>
        δ(name)
    }
  }
}
*/
