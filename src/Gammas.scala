// A Gamma consists of all bound type names,
// a typing function for free variables,
// and a map for bound variables.
trait Gammas extends Unification {
  trait Γ {
    def typevars: Set[δ]
    def termvars: Map[χ, Type]
    def freevars: PartialFunction[ξ, Type]

    def ⊢ (t: Term): Type
  }

  trait Γ_EF extends Γ {
    Γ =>

    def ⊢ (t: Term): Type = t match {
      // (TAUT)
      case x: χ => termvars(x)
      case x: ξ => freevars(x)

      // (∃I)
      case Ξ(t, ex_a_τ) =>
        val τ_with_a_to_σ = Γ ⊢ t
        ???

      // (→∀I)
    }
  }
}
