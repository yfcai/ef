// A Gamma consists of all bound type names,
// a typing function for free variables,
// and a map for bound variables.
trait Gammas extends Terms {
  trait Γ {
    def typevars: Set[δ]
    def termvars: Map[χ, Type]
    def freevars: PartialFunction[ξ, Type]

    def ⊢ (t: Term): Type
  }
}
