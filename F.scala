trait SystemF extends TypedTerms with Substitution {
  object SystemF {
    case class Λ(alpha: Name, body: Term) extends Term
    case class □(term: Term, typeArg: Type) extends Term
  }

  case class FTerm(canon: Term,
                   Γ: PartialFunction[Name, Type],
                   names: Map[Name, Name])
  extends CanonizedTerm
  {
    def getType: Type = getSystemFType(canon, Γ)
  }

  def getSystemFType(canon: Term, Γ: PartialFunction[Name, Type]): Type = {
    import SystemF._
    def loop(canon: Term): Type = canon match {
      case χ(name) =>
        Γ(name)

      case λ(name, body) =>
        Γ(name) →: loop(body)

      case ε(operator, operand) =>
        val σ0 → τ = loop(operator)
        val σ1     = loop(operand)
        if (σ0 != σ1)
          sys error s"""|Operand type mismatch in application $canon:
                        |operator : ${σ0} → ${τ}
                        |operand  : ${σ1}
                        |""".stripMargin
        τ

      case Λ(alpha, body) =>
        ∀(alpha, loop(body))

      case □(term, typeArg) =>
        val ∀(alpha, typeBody) = loop(term)
        typeBody substitute (alpha -> typeArg)
    }
    loop(canon)
  }
}
