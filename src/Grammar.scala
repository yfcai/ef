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

  case object IndividualTokens extends Fixity {
    def splits(tokens: Tokens): Iterator[Seq[Tokens]] =
      IndividualIterator(tokens)

    case class IndividualIterator(tokens: Tokens)
    extends Iterator[Seq[Tokens]] {
      var hasNext = true
      def next =
        if (! hasNext)
          sys error s"next of empty $this"
        else {
          hasNext = false
          tokens map (x => Seq(x))
        }
    }
  }

  case object Juxtaposition extends Fixity {
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
  sealed trait AST
  case class Leaf(tag: Operator, get: Seq[Tokens]) extends AST
  case class Branch(tag: Operator, children: List[AST]) extends AST

  class Operator(fixity: Fixity, toTryNext: Tokens => Seq[Seq[Operator]]) {
    def this(fixity: Fixity, tryNext: => Seq[Seq[Operator]]) =
        this(fixity, _ => tryNext)

    def parse(string: String): Option[AST] = parse(tokenize(string))

    def parse(tokens: Tokens): Option[AST] = {
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
                if (parsersToTry == null) {
                  println(parsersToTry)
                  println(tokens)
                  sys error "?"
                }
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
