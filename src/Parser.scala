trait ExpressionGrammar extends Grammar {
  type Domain = String

  // keywords (always a token by itself):
  val keywords = "( ) [ ] { } ∀ ∃ Λ λ .".words

  // things that can't be a name:
  lazy val forbidden = "( )".words

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
    Postfix("{", "}"),
    Seq(downFrom(TypeInstantiation, termOps),
        Seq(ExistentialQuantification))
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
    Seq(Seq(Atomic), termOps)
  )

  case object TermAbstraction extends Operator(
    Prefix("λ", ":", "."),
    Seq(Seq(Atomic), typeOps, termOps)
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
      TermAbstraction   ,
      TypeAbstraction   ,
      TypeInstantiation ,
      TypeAmnesia       ,
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
  case object ParagraphExpr extends DummyOperator(paragraphOps)

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

  case object TermDeclaration
  extends DefinitionOperator("=", TermExpr)

  // can't set TermParameterList = TypeParameterList
  // because we want to make tag.toString distinct
  // so as not to confuse humans
  case object TermParameterList extends Operator(
    IndividualTokens,
    _ map (_ => Seq(Atomic))
  )

  // we'd want to try TypedFunctionDeclaration last
  // because it fails more slowly than others
  case object TypedFunctionDeclaration extends Operator (
    Infixr("="),
    Seq(Seq(TermParameterList), Seq(TermExpr))
  ) {
    // if "=" comes immediately after a name,
    // then TermDeclaration should take care of it.
    override def precondition(tokens: Tokens) =
      (tokens indexOf "=") > 1
  }

  val paragraphOps: List[Operator] =
    List(
      ParagraphComment,
      TypeSynonym,
      TypeSignature,
      TermDeclaration,
      TypedFunctionDeclaration)
}

// parse file, produce terms and types
trait Parser extends ParagraphGrammar with Terms {
}

object TestParser extends Parser {
  val loremIpsum =
    """|      	
       |
       |.lorem ipsum
       |. dolor sit amet
       |Lorem ipsum
       |                      	
       |dolor sit amet
       | lorem ipsum
       |.yoyo .8
       |  dolor sit amet
       |. okayish
       |lorem ipsum dolor sit amet
       |
       |  . wow
       |  . rant
       |     . this is a fake rant
       |
       |. rant
       |
       |  All the whores and politicians will look
       |  up to me and shout, "save us!"
       |
       |  I will look down and whisper, "no".
       |            	
       |
       |""".stripMargin

  def testParagraphs(s: String, p: Paragraphs) {
    println("TESTING PARAGRAPHS")
    println("==================")
    println(s.lines.zipWithIndex.map({
      case (line, linenum) =>
        "%3d: %s" format (linenum + 1, line)
    }) mkString "\n")
    println
    println(p mkString "\n\n")
    println
  }

  def testParagraphs(s: String) {
    testParagraphs(s, Paragraphs(s))
  }

  def testParagraphsFromFile(path: String) {
    val s = (scala.io.Source fromFile path).getLines mkString "\n"
    testParagraphs(s, Paragraphs fromFile path)
  }

  def thisFile: String =
    new Throwable().getStackTrace().head.getFileName

  def main(args: Array[String]) {
    testParagraphs(loremIpsum)
  }
}
