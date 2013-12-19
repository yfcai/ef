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
        module addDefinition (x.to_ξ, xdef.toProtoChurchTerm.toChurchTerm)

      // typed function definition: requires a signature
      case Branch(TypedFUnctionDefinition,
                  List(Branch(TermParameterList, parameterList), body)) =>
        // do stupid argument extraction for now,
        // do the smart thing after we figure out prenex form
        val lhs :: parameters = parameterList map (_.to_ξ)
        val τ = module Γ lhs
        val protobody = body.toProtoChurchTerm
        val abs = (parameters foldRight protobody.term)({
           case (x, body) => λ(x)(body)
        }).asInstanceOf[λ]
        val argTypes = (parameters, τ.argumentTypes.toSeq).zipped.map {
          case (_, σ) => σ
        }
        if (argTypes.length != parameters.length)
          sys error (s"too many arguments in the definition of:\n"+
            s"${lhs.name} : ${τ.unparse}")
        val rhs = ProtoChurchTerm(
          abs,
          argTypes ++ protobody.annotations
        ).toChurchTerm
        module addDefinition (lhs, rhs)
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
