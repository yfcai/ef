trait SystemF extends TypedModules
    with IntsAndBools with Status with Aliasing with Topology
{
  def typeCheck(m: Module):
      Either[Problem, Seq[(Tree, Tree, Token)]] = ???

  class SystemFTyping(m0: Module) extends SynonymResolution(m0) {
    def getType(Γ: Gamma, t: Tree): Status[Tree] = t match {
      case χ(x) =>
        if (Γ contains x)
          Success(Γ(x))
        else
          Failure(s"undeclared identifier $x")

      case λ(x, σ0, body) =>
        val σ = resolve(σ0)
        getType(Γ.updated(x, σ), body).flatMap(
          τ => Success(→(σ, τ)))

      case f ₋ x =>
        for {
          functionType <- getType(Γ, f)
          _ <- NoReturn
        } yield functionType match {
          case σ → τ =>
            for { σ0 <- getType(Γ, x) ;  _ <- NoReturn } yield
              if (σ0 α_equiv σ)
                Success(τ)
              else
                Failure(
                  s"""|operand type mismatch. operator expects
                      |  ${σ.unparse}
                      |but operand has type
                      |  ${σ0.unparse}
                      |""".stripMargin)
          case nonfunction => Failure(
            s"nonfunction in operator position: ${nonfunction.unparse}")
        }

      case Λ(α, t) =>
        for { τ <- getType(Γ, t) } yield ∀(α, Annotation.none(), τ)

      case t □ σ0 =>
        val σ = resolve(σ0)
        for { τ <- getType(Γ, t) ; _ <- NoReturn } yield τ.tag match {
          case Universal => Success(τ(σ))
          case otherwise => Failure(
            s"cannot instantiate nonuniversal type ${τ.unparse}")
        }
    }
  }
}
