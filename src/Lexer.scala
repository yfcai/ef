trait Lexer {
  def leftParens : Set[String]
  def rightParens: Set[String]

  // keywords (always a token by itself):
  val _leftParens = leftParens
  val _rightParens = rightParens
  val keywords: Set[String] = _leftParens ++ _rightParens

  case class Problem(token: Token, message: String, lines: Int = 3)
      extends Exception(
    s"""|${token.fileLine}
        |${token.residentLines(lines)}
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
      if (paragraph.body.length <= location)
        return ""
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

  def tokenize(p: Paragraph): Seq[Token] = new TokenIterator(p).toSeq

  final def tokenize(s: String): Seq[Token] = tokenize(Paragraph(s))

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
    def hasNext: Boolean = {
      lines = removeEmptyLines(lines)._2
      ! lines.isEmpty
    }
    def next: Paragraph = {
      if (! hasNext) sys error s"next of $this"
      var startOfNextParagraph = nextParagraph(lines)
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

    def nextParagraph(lines: Stream[String]): Int = {
      val next = lines indexWhere (
        // x.head.isSpace must come last;
        // .isLineComment rules out empty strings
        x => x.isParagraphComment || !(x.isLineComment || x.head.isSpace),
        1)
      if (next < 0)
        lines.length
      else
        next
    }


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
      while(! result.isEmpty && result.head.isParagraphComment) {
        val next = nextParagraph(result)
        result = result.drop(next)
        emptyLines += next
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
    def hasBody(t: Tree, op: Any): Boolean = t match {
      case ∙(TokenAST, tok: Token) => op match {
        case op: String => tok.body == op
        case ops: Seq[_] => ops contains tok.body
      }
      case _ => false
    }

    def splitSeq[T](xs: Seq[T], predicate: T => Boolean): Seq[Seq[T]] = {
      val i = xs.indexWhere(predicate)
      if (i < 0)
        Seq(xs)
      else {
        val split = xs.splitAt(i)
        val before = split._1
        val after  = split._2.tail
        before +: splitSeq(after, predicate)
      }
    }
  }

  case class SetLike(lp: Any, sep: Any, rp: Any) extends Fixity {
    def splits(items: Items): Iterator[ItemGroups] = {
      if (items.length >= 2 &&
          hasBody(items.head, lp) &&
          hasBody(items.last, rp)) {
        val chunks = splitSeq[Tree](items.init.tail, t => hasBody(t, sep))
        chunks match {
          case Seq(Seq()) =>
            Iterator(Nil)
          case _ if (chunks.find(_.length == 0) != None) =>
            Iterator.empty
          case _ =>
            Iterator(chunks)
        }
      }
      else {
        Iterator.empty
      }
    }
  }

  case object AllItemsTogether extends Fixity {
    def splits(items: Items) = Iterator(Seq(items))
  }

  trait Juxtaposed extends Fixity

  case object CompositeItem extends Juxtaposed {
    def splits(items: Items): Iterator[ItemGroups] =
      Iterator(Seq(items))
  }

  case object Juxtaposition extends Juxtaposed {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.length >= 2)
        Iterator(Seq(items.init, Seq(items.last)))
      else
        Iterator.empty
  }

  case class Prefix(ops: Any*) extends Fixity {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.isEmpty)
        Iterator.empty
      else if (hasBody(items.head, ops.head))
        Infixr(ops.tail: _*) splits items.tail
      else
        Iterator.empty
  }

  case class Postfix(ops: Any*) extends Fixity {
    def splits(items: Items): Iterator[ItemGroups] =
      if (items.isEmpty)
        Iterator.empty
      else if (hasBody(items.last, ops.last))
        Infixl(ops.init: _*) splits items.init
      else
        Iterator.empty
  }

  case class LoneToken(predicate: String => Boolean) extends Fixity {
    def splits(items: Items) = items match {
      case Seq(∙(TokenAST, token: Token))
          if predicate(token.body) =>
        Iterator(Seq(items))
      case _ =>
        Iterator.empty
    }
  }

  object LoneToken {
    def forbid(forbidden: Set[String]): LoneToken =
      LoneToken(x => ! forbidden.contains(x))
  }

  case object LoneTree extends Fixity {
    def splits(items: Items) = items match {
      case Seq(t: ⊹) =>
        Iterator(Seq(items))
      case _ =>
        Iterator.empty
    }
  }

  case class Infixr(ops: Any*) extends Infix {
    def cloneMyself = Infixr.apply
    def initialHeadPosition(items: Items) = 0
    def nextHeadPosition(items: Items, headPosition: Int): Int =
      items.indexWhere(x => hasBody(x, ops.head), headPosition + 1)
  }

  case class Infixl(ops: Any*) extends Infix {
    def cloneMyself = Infixl.apply
    def initialHeadPosition(items: Items) = items.length - 1
    def nextHeadPosition(items: Items, headPosition: Int): Int =
      items.lastIndexWhere(x => hasBody(x, ops.head), headPosition - 1)
  }

  trait Infix extends Fixity {
    def ops: Seq[Any]
    def cloneMyself: Seq[Any] => Infix
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
  trait DelegateOperator extends Operator {
    def delegate: Operator
    def genus: Genus

    def fixity = delegate.fixity
    def tryNext = delegate.tryNext
    def cons(children: Seq[Tree]) = delegate.cons(children)
    override def parse(items: Seq[Tree]) = delegate.parse(items)
    override def unparse(t: Tree) = delegate.unparse(t)
  }

  trait Operator extends Tag {
    def fixity: Fixity
    def tryNext: Seq[Seq[Operator]]
    def genus: Genus

    def tryNextOverride: Seq[Seq[Tree]] => Seq[Seq[Operator]] =
      _ => tryNext

    /** @param children
      * is the sequence of proto-ASTs allotted to this node if it
      * is a leaf, and is the sequence of children if it is not.
      */
    def cons(children: Seq[Tree]): Tree
    def decons(t: Tree): Seq[Tree] = t.children

    // extension point to introduce fast failures
    def precondition(items: Seq[Tree]): Boolean = true

    final def parse(string: String): Option[Tree] =
      parse(ProtoAST(string)).map(_._1)

    // @return None or Some((AST, first token of construct in preorder))
    def parse(items: Seq[Tree]): Option[(Tree, List[Token])] = {
      if (precondition(items) == false)
        return None

      val splits = fixity splits items

      while(splits.hasNext) {
        val split = splits.next
        val tryNext = tryNextOverride(split)
        if (tryNext.isEmpty) {
          // produce a leaf
          split match {
            case Seq(x) =>
              return Some((cons(x), List(getFirstToken(items))))
            case Seq() =>
              return Some((cons(Nil), List(getFirstToken(items))))
            case _ =>
              sys error s"leaf operator with nonunary fixity: $this"
          }
        }
        else {
          // produce a branch
          // assertion to locate buggy operators
          if(split.length != tryNext.length)
            sys error s"""operator $this declares arity ${
              split.length
            } but has ${tryNext.length} children"""
          val maybeChildren =
            (tryNext, split).zipped.foldRight(
              Some(Nil): Option[List[(Tree, List[Token])]]
            ) {
              case ((_, _), None) => None
              case ((parsersToTry, items), Some(bros)) =>
                parsersToTry.findFirst(_ parse items).map(_ :: bros)
            }
          // if a feasible split is found, do not try other,
          // less preferable, splits.
          maybeChildren match {
            case None => ()
            case Some(children) => return Some((
              cons(children.map(_._1)),
              chooseToken(fixity, split, items) :: children.flatMap(_._2)
            ))
          }
        }
      }
      // I can't parse it
      None
    }

    def chooseToken(fixity: Fixity, split: Seq[Seq[Tree]], items: Seq[Tree]):
        Token = (fixity, split) match {
      case (Infixl(_*), Seq(_*)) | (Infixr(_*), Seq(_*)) =>
        getFirstToken(items.drop(split.head.length))
      case _ =>
        getFirstToken(items)
    }

    def getFirstToken(ts: Seq[Tree]): Token =
      ts.findFirst(getFirstToken).get

    def getFirstToken(t: Tree): Option[Token] = t match {
      case x @ ∙(TokenAST, _) => Some(x.as[Token])
      case x @ ⊹(_, children @ _*) => children.findFirst(getFirstToken)
      case _ => None
    }

    override def unparse(t: Tree): String =
      t match {
      case ⊹(operator: Operator, _*) =>
        val children = decons(t)
        val tokens = children map (x => x.tag unparse x)
        val subops = operator.tryNext
        val parens = ((children map (_.tag), tokens).zipped, subops).zipped.
          map({
            case ((childOp, child), subOps) => childOp match {
              case _: LeafTag => child
              case _ if (subOps contains childOp) => child
              case _ => s"($child)"
            }
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

    private[this]
    def pack(tokens: Seq[String]): String =
      (tokens.head +: ((tokens, tokens.tail).zipped.flatMap {
        case (before, after)
            if (_leftParens contains before)
            || (_rightParens contains after) =>
          List(after)
        case (_, after) =>
          List(" ", after)
      })).mkString

    private[this]
    def prefixLike(ops: Seq[Any], children: Seq[String]): Seq[String] =
      (ops, children).zipped flatMap {
        case (op: String, child) => List(op, child)
        case (op: Seq[_], child) => List(op.head.toString, child)
      }

    private[this]
    def postfixLike(ops: Seq[Any], children: Seq[String]): Seq[String] =
      (ops, children).zipped flatMap {
        case (op: String, child) => List(child, op)
        case (op: Seq[_], child) => List(child, op.head.toString)
      }
  }

  trait BinderOperator extends Operator with Binder {
    def cons(children: Seq[Tree]): Tree =
      this.bind(children.head.as[String], children.tail: _*)

    override def decons(t: Tree): Seq[Tree] =
      unbind(t).get match { case (x, bodies) => x +: bodies }
  }

  trait LeafOperator extends Operator with LeafTag {
    def fixity: Fixity
    def genus: Genus
    def man: Manifest[_]

    def cons(children: Seq[Tree]): Tree
    def unparseLeaf(leaf: ∙[_]): String

    override def tryNext = Seq.empty[Seq[Operator]]
  }

  trait FoldableWithTokens {
    def fold[T](f: (TreeF[T], Token) => T): T
  }

  def withTokens(t: Tree, toks: Seq[Token]):
      FoldableWithTokens = new FoldableWithTokens {
    def fold[T](f: (TreeF[T], Token) => T): T = foldWithTokens(t, toks, f)
  }

  def foldWithTokens[T]
      (t: Tree, _toks: Seq[Token], f: (TreeF[T], Token) => T): T = {
    var toks = _toks
    def loop(t: Tree): T = {
      val tok = toks.head
      toks = toks.tail
      t match {
        case ∙(tag, get) =>
          f(∙:(tag, get), tok)
        case ⊹(tag, children @ _*) =>
          f(⊹:(tag, children.map(loop): _*), tok)
      }
    }
    loop(t)
  }
}
