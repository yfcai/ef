trait Types extends Trees {
  case object Type extends Genus
  // æ
}

trait Terms extends Types {
  // terms, no boilerplate
  case object Term extends Genus
  // try make them operators
  /*
  case object FreeVar extends FreeName(Term)
  case object Var extends DeBruijn(Term)
  case object Abs extends Binder(Var, Term, Term)
  case object App extends Tag(Term, Term, Term)

  // extrapolate BinderFactory after more examples
  object λ {
    def apply(x: String)(body: Tree): Tree =
      ⊹(Abs, §(x), body.imprison(Var, x, 0))
  }
  object χ extends LeafFactory[String](FreeVar)
   */
}
