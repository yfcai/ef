/** first order unification, works well for monotypes */
trait Unification extends Syntax {
  trait Status[+T] {
    def toBoolean: Boolean
    def get: T
    def map[R](f: T => R): Status[R]
  }

  case class Success[+T](get: T) extends Status[T] {
    def toBoolean: Boolean = true
    def map[R](f: T => R): Status[R] = Success(f(get))
  }

  case class Failure[+T](message: String) extends Status[T] {
    def toBoolean: Boolean = false
    def map[R](f: T => R): Status[R] = Failure(message)

    def get: T = sys error s"get of $this"
  }

  def unifyMonotypes(degreesOfFreedom: Set[String], monotypes: Tree*):
      Status[Map[String, Tree]] =
    if (monotypes.isEmpty)
      Success(Map.empty)
    else
      resolveConstraints(degreesOfFreedom,
        monotypes.tail.map(_ ≡ monotypes.head))

  def unifySubstitutions(lhs: Map[String, Tree], rhs: Map[String, Tree]):
      Status[Map[String, Tree]] = {
    val conflicts = lhs.keySet & rhs.keySet
    ???
  }

  // equality constraints
  case class ≡(lhs: Tree, rhs: Tree) {
    override def toString = s"${lhs.unparse}  ≡  ${rhs.unparse}"
  }
  implicit class makeEqualityConstraint(lhs: Tree) {
    def ≡(rhs: Tree) = new ≡(lhs, rhs)
  }

  /** @param dof degrees of freedom
    */
  def resolveConstraints(dof: Set[String], constraints: Seq[≡]):
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
          loop(rest map {
            case lhs ≡ rhs => (lhs.subst(æ(α), τ)) ≡ (rhs.subst(æ(α), τ))
          }).map(mgs => mgs.updated(α, τ subst mgs))

      case τ ≡ æ(α) :: rest if (dof contains α) =>
        loop(æ(α) ≡ τ :: rest)

      case Nil =>
        Success(Map.empty[String, Tree])

      // error cases
      case σ ≡ τ :: _ =>
        Failure(
          """|missing case in monotype unification:
             |${σ.unparse}
             |${τ.unparse}"
             |""".stripMargin)
    }
    loop(constraints.toList)
  }
}
