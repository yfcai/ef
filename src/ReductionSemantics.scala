trait ReductionSemantics extends Syntax {
  type Reduction = PartialFunction[Tree, Tree]

  // values
  object Val {
    def unapply(t: Tree): Option[Tree] = t.tag match {
      case AnnotatedAbstraction | FreeVar =>
        Some(t)
      case _ =>
        None
    }
  }

  // evaluation context: call-by-value
  def evalContext(t: Tree): (Tree, Tree => Tree) = t match {
    case Val(v) ₋ e =>
      val (e2, c) = evalContext(e)
      (e2, x => ₋(v, c(x)))
    case e0 ₋ e1 =>
      val (e2, c) = evalContext(e0)
      (e2, x => ₋(c(x), e1))
    case _ =>
      (t, x => x)
  }

  // untyped β-reduction
  val beta: Reduction = {
    // not using λ here due to inherent unbinding involved
    case ₋(f, x) if f.tag == AnnotatedAbstraction => f(x)
  }

  // ignore top-level type annotations
  val erasure: Reduction = {
    case t if t.tag == TypeAbstraction =>
      TypeAbstraction.bodyOf(t)
    // ascription
    case Å(t, τ) =>
      t
    // instantiation
    case □(t, σ) =>
      t
  }

  val delta: Reduction = ???
}
