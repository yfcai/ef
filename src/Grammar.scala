trait Lexer {
  type Token  = String
  type Tokens = Seq[Token]

  // keywords (always a token by itself):
  def keywords: Set[String]

  def tokenize(s: String): Tokens = new TokenIterator(s).toSeq

  class TokenIterator(var remains: String) extends Iterator[Token] {
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

    def foundNextToken(from: Int, token: Token) {
      nextToken = token
      remains = remains substring (from + token.length, remains.length)
    }
  }

  implicit class CharOps(c: Char) {
    import java.lang.Character
    def isSpace = Character.isWhitespace(c)
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
}

trait Fixities extends Lexer {
  trait Fixity {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]]

    object NoWay extends Iterator[Seq[Tokens]] {
      def next = sys error s"Nope, got nothin'"
      def hasNext = false
    }

    case class Singleton(tokens: Tokens) extends Iterator[Seq[Tokens]] {
      var hasNext = true
      def next: Seq[Tokens] =
        if (hasNext) {
          hasNext = false
          Seq(tokens)
        }
        else sys error s"next of $this"
    }
  }

  case object AllTokensTogether extends Fixity {
    def splits(tokens: Tokens) = Singleton(tokens)
  }

  trait Juxtaposed extends Fixity

  case object IndividualTokens extends Juxtaposed {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      IndividualIterator(tokens)

    case class IndividualIterator(tokens: Tokens)
    extends Iterator[Seq[Tokens]] {
      var hasNext = ! tokens.isEmpty
      def next =
        if (! hasNext)
          sys error s"next of empty $this"
        else {
          hasNext = false
          tokens map (x => Seq(x))
        }
    }
  }

  case object Juxtaposition extends Juxtaposed {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      Juxtapositor(tokens)

    case class Juxtapositor(tokens: Tokens) extends Iterator[Seq[Tokens]] {
      var toSplitAt: Int = tokens.length - 1
      def hasNext = toSplitAt > 0
      def next = {
        val result = tokens splitAt toSplitAt
        toSplitAt -= 1
        Seq(result._1, result._2)
      }
    }
  }

  case class Prefix(ops: Token*) extends Fixity {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      if (tokens.isEmpty)
        NoWay
      else if (ops.head == tokens.head)
        toInfix splits tokens.tail
      else
        NoWay

    val toInfix: Infix = Infixr(ops.tail: _*)
  }

  case class Postfix(ops: Token*) extends Fixity {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      if (tokens.isEmpty)
        NoWay
      else if (ops.last == tokens.last)
        toInfix splits tokens.init
      else
        NoWay

    val toInfix: Infix = Infixl(ops.init: _*)
  }

  case class Enclosing(ops: Token*) extends Fixity {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      if (ops.head == tokens.head && ops.last == tokens.last)
        toInfix splits tokens.tail.init
      else
        NoWay

    // hm. not sure whether to use Infixr or Infixl
    val toInfix: Infix = Infixr(ops.tail.init: _*)
  }

  case class LoneToken(forbidden: Set[Token]) extends Fixity {
    def splits(tokens: Tokens) = tokens match {
      case Seq(token) if ! (forbidden contains token) =>
        Singleton(Seq(token))
      case _ => NoWay
    }
  }

  case class Infixr(ops: Token*) extends Infix {
    def cloneMyself(ops: Seq[Token]) = Infixr(ops: _*)
    def initialHeadPosition(tokens: Tokens) = 0
    def nextHeadPosition(tokens: Tokens, headPosition: Int): Int =
      tokens indexOf (ops.head, headPosition + 1)
  }

  case class Infixl(ops: Token*) extends Infix {
    def cloneMyself(ops: Seq[Token]) = Infixl(ops: _*)
    def initialHeadPosition(tokens: Tokens) = tokens.length - 1
    def nextHeadPosition(tokens: Tokens, headPosition: Int): Int =
      tokens lastIndexOf (ops.head, headPosition - 1)
  }

  trait Infix extends Fixity {
    def ops: Seq[Token]
    def cloneMyself(ops: Seq[Token]): Infix
    def initialHeadPosition(tokens: Tokens): Int
    def nextHeadPosition(tokens: Tokens, headPosition: Int): Int


    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      if (tokens.isEmpty)
        NoWay
      else if (ops.isEmpty)
        Singleton(tokens)
      else
        InfixIterator(tokens)

    case class InfixIterator(tokens: Tokens) extends Iterator[Seq[Tokens]] {
      var headPosition = initialHeadPosition(tokens)

      val suffix = cloneMyself(ops.tail)

      var suffixIterator: Iterator[Seq[Tokens]] = NoWay

      var nextCandidate: Seq[Tokens] = null

      var thisPortion: Tokens = null

      // precondition: suffixIterator.hasNext && thisPortion != null
      def resultFromSuffix(): Seq[Tokens] =
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
        headPosition = nextHeadPosition(tokens, headPosition)
        // this iterator becomes exhausted; do nothing
        if (headPosition < 0) return ()
        // found next head. time to construct suffixIterator.
        val (beforeHead, headAndMore) = tokens splitAt headPosition
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

      def next: Seq[Tokens] = {
        tryToFindNextCandidate()
        if (nextCandidateNotFound) sys error s"next of empty $this"
        val result = nextCandidate
        resetNextCandidate()
        result
      }
    }
  }
}

trait Grammar extends Fixities {
  // AST is decoupled from specific grammars
  trait AST {
    def tag: Operator

    def unparse: String = this match {
      case Branch(operator, children) =>
        val tokens = children map (_.unparse)
        val subops = operator toTryNext tokens
        val parens = ((children map (_.tag), tokens).zipped, subops).zipped.
          map({ case ((childOp, child), subOps) =>
            if (subOps contains childOp)
              child
            else
              s"($child)"
          }).toSeq
        pack(operator.fixity match {
          case _: Juxtaposed =>
            parens
          case p: Prefix     =>
            prefixLike (p.ops, parens)
          case p: Postfix    =>
            postfixLike(p.ops, parens)
          case i: Infix      =>
            parens.head +: prefixLike(i.ops, parens.tail)
          case e: Enclosing  =>
            e.ops.head +: postfixLike(e.ops.tail, parens)
        })

      case Leaf(_, seq) =>
        pack(seq map pack)
    }

    // duplicates partial info in keyword. how to merge?
    private
    val leftParens  = Set("{", "[", "λ", "Λ", "∀", "∃")
    private
    val rightParens = Set("}", "]", ".")

    private[this]
    def pack(tokens: Seq[String]): String =
      (tokens.head +: ((tokens, tokens.tail).zipped.flatMap {
        case (before, after)
            if (leftParens contains before)
            || (rightParens contains after) => List(after)
        case (_, after) =>
          List(" ", after)
      })).mkString

    private[this]
    def prefixLike(ops: Tokens, children: Tokens): Tokens =
      (ops, children).zipped flatMap {
        case (op, child) => List(op, child)
      }

    private[this]
    def postfixLike(ops: Tokens, children: Tokens): Tokens =
      prefixLike(children, ops)
  }

  case class Leaf(tag: Operator, get: Seq[Tokens]) extends AST
  case class Branch(tag: Operator, children: List[AST]) extends AST

  class Operator(
    val fixity: Fixity,
    val toTryNext: Tokens => Seq[Seq[Operator]])
  {
    def this(fixity: Fixity, tryNext: => Seq[Seq[Operator]]) =
        this(fixity, _ => tryNext)

    def precondition(tokens: Tokens): Boolean = true

    def parse(string: String): Option[AST] = parse(tokenize(string))

    def parse(tokens: Tokens): Option[AST] = {
      if (! precondition(tokens)) return None
      val splits = fixity splits tokens
      val tryNext = toTryNext(tokens)
      if (tryNext.isEmpty) {
        // nothing to try next, produce a leaf.
        if (splits.hasNext)
          Some(Leaf(this, splits.next))
        else
          None
      }
      else {
        // got stuff to try next, produce a branch.
        while(splits.hasNext) {
          val split = splits.next
          // assertion to locate buggy operators
          assert(split.length == tryNext.length)
          val maybeChildren: Option[List[AST]] =
            (tryNext, split).zipped.foldRight[Option[List[AST]]](
              Some(Nil)
            ) {
              case ((_, _), None) => None
              case ((parsersToTry, tokens), Some(bros)) =>
                parsersToTry findFirst (_ parse tokens) map (_ :: bros)
            }
          // if a feasible split is found, do not try other,
          // less preferable, splits.
          maybeChildren match {
            case None => ()
            case Some(children) => return Some(Branch(this, children))
          }
        }
        // I can't parse it.
        return None
      }
    }
  }
}

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

/** Chop file into paragraphs. A paragraph is a continguous set
  * of lines such that the first line starts with a nonspace and
  * the other lines start with a space.
  */
trait Paragraphs extends Lexer {
  case class Paragraph(line: Int, body: String)

  object Paragraphs {
    def apply(s: String): Paragraphs =
      apply(s.lines)
    def fromFile(path: String): Paragraphs =
      apply(scala.io.Source.fromFile(path).getLines)
  }

  case class Paragraphs(_lines: Iterator[String])
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
        thisLineNumber,
        (thisParagraph filterNot (_.isLineComment)) mkString "\n"
      )
    }

    var lines: Stream[String] = null
    var nextLineNumber = 0

    {
      val (int, stream) = removeEmptyLines(_lines.toStream)
      lines = stream
      nextLineNumber = int + 1 // first line is line 1
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
