// parse file, produce terms and types
trait Parser extends ParagraphGrammar with ASTConversions with Syntax {
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
    paragraph match {
      // the paragraph is a rant, do nothing
      case Leaf(ParagraphComment, _) =>
        module

      // type synonym: add binding now, resolve circularity later
      case Branch(TypeSynonym,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        val lhs :: parameters = parameterList map (_.to_δ)
        val rhs = ∀(parameters, body.toType)
        module addSynonym (lhs, rhs)

      // type signature: add binding now, instantiate later
      case Branch(TypeSignature, List(x, xtype)) =>
        module addSignature (x.to_ξ, xtype.toType)

      // term definition: add binding now, verify type later
      case Branch(TermDefinition, List(x, xdef)) =>
        module addDefinition (x.to_ξ, xdef.toChurchTerm)

      // typed function definition: requires a signature
      case Branch(TypedFUnctionDefinition,
                  List(Branch(TermParameterList, parameterList), body)) =>
        // do stupid argument extraction for now,
        // do the smart thing after we figure out prenex form
        val lhs :: parameters = parameterList map (_.to_ξ)
        val τ = module Γ lhs
        val ChurchTerm(oldTerm, oldAnnotations) = body.toChurchTerm
        val abs = (parameters foldRight oldTerm)({
           case (x, body) => λ(x)(body)
        }).asInstanceOf[λ]
        val typedArgs = (abs.detachNestedDoppelgaenger._1,
                         τ.argumentTypes.toSeq).zipped.toSeq
        if (typedArgs.length != parameters.length)
          sys error s"too many arguments in the definition of:\n$lhs : $τ"
        // hack the annotations for now.
        // need α-equivalence to be robust.
        // FIXME: breaks on shadowing. aaaaaah.
        val nameToAbs: Map[String, λ] = getLambdas(abs).map({
          lambda => (lambda.name, lambda)
        })(collection.breakOut)
        val annotations = oldAnnotations.map({
          case (x, τ) => (nameToAbs(x.name), τ)
        }) ++ typedArgs.asInstanceOf[Seq[(λ, Type)]]
        module addDefinition (lhs, ChurchTerm(abs, annotations))
    }

  private[this]
  def getLambdas(t: Term): List[λ] = t match {
    case x @ λ(_, body) => x :: getLambdas(body)
    case ₋(f, x) => getLambdas(f) ++ getLambdas(x)
    case □(t, _) => getLambdas(t)
    case Ξ(t, _) => getLambdas(t)
    case _ => Nil
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

  val paragraphs = rant +
    """|type List α = ∀β. β → (α → β → β) → β
       |cons : ℤ → List ℤ → List ℤ
       |five = (Λα. λx : ℤ. + 2 2) [ℤ] 5 {∃α. α}
       |cons x xs = λz : β. λ++ : (α → β → β). ++ x (xs z ++)
       |""".stripMargin

/*
 */
  def main(args: Array[String]) {
    val module = parse(paragraphs)
    println(module.unparse)
  }
}
