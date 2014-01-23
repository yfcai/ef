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

  /** @return (thing inside context, evalutation context)
    *
    * (This is unclear. Investigate how best to implement
    * evaluation contexts.)
    */
  def callByValue(t: Tree)(isRedex: Tree => Boolean):
      (Tree, Tree => Tree) = t match {
    case e if isRedex(e) =>
      (e, x => x)
    case e0 ₋ e1 if isRedex(e0) =>
      (e0, x => ₋(x, e1))
    case Val(v) ₋ e =>
      val (e2, c) = callByValue(e)(isRedex)
      (e2, x => ₋(v, c(x)))
    case e0 ₋ e1 =>
      val (e2, c) = callByValue(e0)(isRedex)
      if (isRedex(e2))
        (e2, x => ₋(c(x), e1))
      else {
        val (e3, c) = callByValue(e1)(isRedex)
        (e3, x => ₋(e0, c(x)))
      }
    case e =>
      (e, x => x)
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

  val delta: Reduction = {
    // arithmetics
    case (χ("+") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt + rhs.toInt).toString)
    case (χ("-") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt - rhs.toInt).toString)
    case (χ("*") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt * rhs.toInt).toString)
    case (χ("/") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt / rhs.toInt).toString)
    case (χ("%") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt % rhs.toInt).toString)
    // integer comparisons
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≡" || op == "==" =>
      χ((lhs.toInt == rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "<" =>
      χ((lhs.toInt < rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == ">" =>
      χ((lhs.toInt > rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≤" || op == "<=" =>
      χ((lhs.toInt <= rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≥" || op == ">=" =>
      χ((lhs.toInt >= rhs.toInt).toString)
    // Church-encoded Booleans
    case (χ("true")  ₋ thenBranch) ₋ elseBranch =>
      thenBranch
    case (χ("false") ₋ thenBranch) ₋ elseBranch =>
      elseBranch
    // loops, coz recursion's too hard
    case ((χ("iterate") ₋ χ(n)) ₋ z) ₋ f =>
      Range(n.toInt, 0, -1).foldRight(z) {
        case (i, body) => ₋(₋(f, χ(i.toString)), body)
      }
    // absurdity
    case χ("???") ₋ _ =>
      sys error s"applying absurdity"
  }

  val reduction: Reduction = beta orElse delta orElse erasure

  def reduce(t: Tree, env: PartialFunction[String, Tree]):
      Option[Tree] = {
    val realReduction: Reduction = reduction orElse {
      case χ(name) if env.isDefinedAt(name) =>
        env(name)
    }
    val (redex, context) = callByValue(t)(realReduction.isDefinedAt)
    realReduction.andThen(Some.apply[Tree]).
      applyOrElse(redex, (_: Tree) => None).map(context)
  }

  def eval(env: PartialFunction[String, Tree])(t: Tree): Tree =
    reduce(t, env).fold(t)(eval(env))
}
