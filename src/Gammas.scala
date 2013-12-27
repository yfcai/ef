// A Gamma consists of all bound type names,
// a typing function for free variables,
// and a map for bound variables.
trait Gammas extends Unification {
  trait Γ {
    def typevars: Set[Type.FreeName[Type]]
    def termvars: Map[λ, Type]
    def freevars: PartialFunction[ξ, Type]

    def ⊢ (t: Term): Type

    implicit class UnparseTermInTypingContext(t: Term) {
      def unparse: String = ChurchTerm(t, termvars).unparse
    }
  }

  case class Γ_EF(
    typevars: Set[Type.FreeName[Type]],
    termvars: Map[λ, Type],
    freevars: PartialFunction[ξ, Type]
  ) extends Γ {
    Γ =>

    def ⊢ (t0: Term): Type = t0 match {
      // (TAUT)
      case χ(x) =>
        termvars(x)

      case x: ξ if freevars isDefinedAt x =>
        freevars(x)

      // (ascription)
      case Ξ(t, τ_ascribed) =>
        val τ = Γ ⊢ t
        if (τ ⊑ τ_ascribed)
          τ_ascribed
        else
          TypeError {
            s"""|incompatible type ascription:
                |  ${t0.unparse}
                |real type is:
                |  ${τ.unparse}
                |""".stripMargin
          }

      // (→∀I)
      case x @ λ(_, body) =>
        val toQuantify = termvars(x).freeNames -- typevars
        val σ = termvars(x)
        val τ = Γ_EF(typevars ++ toQuantify, termvars, freevars) ⊢ body
        ∀(toQuantify, σ →: τ)

      // (→∀∃E)
      case s ₋ t =>
        val funType = Γ ⊢ s
        val argType = Γ ⊢ t
        getResultTypeOfApplication(funType, argType)

      case _ =>
        TypeError { s"${t0.unparse} is untypeable" }
    }
  }

  object Γ_ℤ extends ℤ_Ring {
    def apply(c: ChurchTerm): Γ_EF =
      Γ_EF(Set(ℤ), c.annotations, ℤ_lit_arith)

    // abstract over?
    def ⊢ (c: ChurchTerm): Type = Γ_ℤ(c) ⊢ c.term
  }

  trait ℤ_Ring {
    val ℤ = δ("ℤ")

    val ℤ_literal = """(-)?\d+"""

    val ℤ_lit_arith: PartialFunction[ξ, Type] = {
      case ξ(s) if s matches ℤ_literal =>
        ℤ

      case ξ("+") | ξ("-") | ξ("*") | ξ("/") =>
        ℤ →: ℤ →: ℤ
    }
  }
}
