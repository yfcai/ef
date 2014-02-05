// try 1: big step
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
    case Ascr(t, τ) =>
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

// try 2: small-step for System F with primitive lists
trait SmallStepSemantics extends SystemF with PrimitiveLists {
  type Reduction = PartialFunction[Tree, Tree]

  /** @return (thing inside context, evalutation context) */
  def callByName(t: Tree, reduction: Reduction):
      (Tree, Tree => Tree) =
    getRedex(t, reduction).getOrElse((t, identity))

  def getRedex(t: Tree, reduction: Reduction):
      Option[(Tree, Tree => Tree)] =
    t match {
      // reduce first, ask questions later
      case _ if reduction isDefinedAt t =>
        Some((t, identity))

      case s ₋ t =>
        getRedex(s, reduction) match {
          case Some((redex, context)) =>
            Some((redex, x => ₋(context(x), t)))
          case None => getRedex(t, reduction).map {
            case (redex, context) => (redex, x => ₋(s, context(x)))
          }
        }

      case t □ τ =>
        getRedex(t, reduction).map {
          case (redex, context) => (redex, x => □(context(x), τ))
        }

      case _ =>
        None
    }

  def step(t: Tree, reduction: Reduction): Option[Tree] = {
    val (redex, context) = callByName(t, reduction)
    if (reduction isDefinedAt redex)
      Some(context(reduction(redex)))
    else
      None
  }

  def eval(t: Tree, reduction: Reduction): Tree = {
    // this elegant thing causes stack overflow when sorting
    // a list of 4 elements.
    //   step(t, reduction).fold(t)(s => eval(s, reduction))
    var current: Tree = null
    var next: Option[Tree] = Some(t)
    do {
      current = next.get
      next = step(current, reduction)
    }
    while (next != None)
    current
  }

  case class Stuck(s: String = "stuck") extends Exception(s)

  // untyped β-reduction
  val beta: Reduction = {
    // not using λ here due to inherent unbinding involved
    case f ₋ x if f.tag == AnnotatedAbstraction => f(x)
  }

  val instantiation: Reduction = {
    case t □ τ if t.tag == TypeAbstraction => t(τ)
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
    case ((χ("true" ) □ _)  ₋ thenBranch) ₋ elseBranch =>
      thenBranch
    case ((χ("false") □ _) ₋ thenBranch) ₋ elseBranch =>
      elseBranch
    // loops, coz recursion's too hard
    case (((χ("iterate") □ τ) ₋ χ(n)) ₋ z) ₋ f =>
      val i = n.toInt
      if (i == 0)
        z
      else if (i > 0)
        ₋(₋(₋(□(χ("iterate"), τ), χ((i - 1).toString)),
          ₋(₋(f, χ(n)), z)), f)
      else
        χ("???")
    // absurdity
    case χ("???") ₋ _ =>
      throw Stuck("applying absurdity")
    case χ("???") □ _ =>
      throw Stuck("instantiating absurdity")

    // lists
    case (χ("isnil") □ _) ₋ (χ("nil") □ _) =>
      χ("true")

    case (χ("isnil") □ _) ₋ (((χ("cons") □ _) ₋ _) ₋ _) =>
      χ("false")

    case (χ("head") □ _) ₋ (χ("nil") □ _) =>
      throw Stuck("head of empty list")

    case (χ("head") □ _) ₋ (((χ("cons") □ _) ₋ head) ₋ _) =>
      head

    case (χ("tail") □ _) ₋ (χ("nil") □ _) =>
      throw Stuck("tail of empty list")

    case (χ("tail") □ _) ₋ (((χ("cons") □ _) ₋ _) ₋ tail) =>
      tail
  }
}
