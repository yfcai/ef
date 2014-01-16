/** first order unification, works well for monotypes */
trait Unification extends Syntax with Status {
  def unifyMonotypesBy(
    index: String => Int,
    degreesOfFreedom: Set[String],
    monotypes: Tree*):
      Status[Map[String, Tree]] =
    if (monotypes.isEmpty)
      Success(Map.empty)
    else
      resolveConstraintsBy(index, degreesOfFreedom,
        monotypes.tail.map(_ ≡ monotypes.head))

  // equality constraints
  case class ≡(lhs: Tree, rhs: Tree) {
    override def toString = s"${lhs.unparse}  ≡  ${rhs.unparse}"
  }
  implicit class makeEqualityConstraint(lhs: Tree) {
    def ≡(rhs: Tree) = new ≡(lhs, rhs)
  }

  /** @param dof degrees of freedom
    */
  def resolveConstraintsBy(
    index: String => Int,
    dof: Set[String],
    constraints: Seq[≡]):
      Status[Map[String, Tree]] =
  {
    type Domain = Status[Map[String, Tree]]
    def loop(constraints: List[≡]): Domain = constraints match {
      case (σ1 → τ1) ≡ (σ2 → τ2) :: rest =>
        loop(σ1 ≡ σ2 :: τ1 ≡ τ2 :: rest)

      case (σ1 ₌ τ1) ≡ (σ2 ₌ τ2) :: rest =>
        loop(σ1 ≡ σ2 :: τ1 ≡ τ2 :: rest)

      case æ(a1) ≡ æ(a2) :: rest if a1 == a2 =>
        loop(rest)

      case æ(α) ≡ τ :: rest if (dof contains α) =>
        // prefer names with a smaller index in the domain
        val (β, σ) = τ match {
          case æ(β) if (dof contains β) && index(β) < index(α) =>
            (β, æ(α))
          case _ =>
            (α, τ)
        }
        loop(rest map {
          case lhs ≡ rhs => (lhs.subst(æ(β), σ)) ≡ (rhs.subst(æ(β), σ))
        }).map(mgs => mgs.updated(β, σ subst mgs))

      case τ ≡ æ(α) :: rest if (dof contains α) =>
        loop(æ(α) ≡ τ :: rest)

      case Nil =>
        Success(Map.empty[String, Tree])

      // error cases
      case σ ≡ τ :: _ =>
        Failure(
          s"""|Cannot unify the following types:
              |  ${σ.unparse}
              |  ${τ.unparse}
              |""".stripMargin)
    }
    loop(constraints.toList)
  }
}
