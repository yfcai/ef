// parse file, produce terms and types
trait Parser extends ParagraphGrammar with Modules {
  def parse(s: String): Module =
    parseParagraphs(ParagraphExpr(s))

  def parseFile(path: String): Module =
    parseParagraphs(ParagraphExpr fromFile path)

  def parseParagraphs(paragraphs: Iterator[AST]): Module =
    (paragraphs foldLeft Module.empty) {
      case (module, nextParagraph) =>
        processParagraph(nextParagraph, module)
    }

  // starts with an immature module and make it more mature
  def processParagraph(paragraph: AST, module: Module): Module =
    paragraph.tag match {
      // the paragraph is a rant, do nothing
      case ParagraphComment =>
        module
    }
}

object TestParser extends Parser {
  val rant =
    """|. rant
       |
       |  All the whores and politicians will look
       |  up to me and shout, "save us!"
       |
       |  I will look down and whisper, "no".
       |""".stripMargin

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
       |""".stripMargin + rant

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

  val paragraphs =
    List(
      rant,
      "type List α = ∀β. β → (α → β → β) → β",
      "cons : ∀α. α → List α → List α",
      "four = let two = 2 in + two two",
      "cons x xs = λz : β. λ++ : (α → β → β). ++ x (xs z ++)"
    )

  def main(args: Array[String]) {
    val s = "y = let x = 5 in + x 1"
    paragraphs foreach { paragraph =>
      println(paragraph)
      println(ParagraphExpr parse paragraph)
      println
    }
  }
}
