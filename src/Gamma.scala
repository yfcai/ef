// A Gamma consists of all bound type names,
// a typing function for free variables,
// and a map for bound variables.
trait Gamma extends Terms {
  case class Γ(
    typevars: Set[δ],
    termvars: Map[χ, Type],
    freevars: PartialFunction[ξ, Type]
  ) {
    // add methods here as they become necessary
  }
}
