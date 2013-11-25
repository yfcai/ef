trait SystemMF
extends TypedTerms with MinimalQuantification with MostGeneralSubstitution
{
  case class SMFTerm(
    canon: Term,
    Γ    : PartialFunction[Name, Type],
    names: Map[Name, Name]
  )
  extends TypedTerm {
    def getTerm: Term = canon renameAll names
    def getType: Type = ???
  }

  // UNIFYING QUANTIFIED TYPES


}

trait MostGeneralSubstitution extends Substitution {
  case class EqConstraint(lhs: Type, rhs: Type)

  def mostGeneralSubstitution(
    constraints: List[EqConstraint]
  ): Map[Name, Type] =
    mostGeneralSubstitution(constraints, new UniversalSet[Name])

  def mostGeneralSubstitution(
    constraints: List[EqConstraint],
    against: Set[Name]
  ): Map[Name, Type] =
  {
    type Eq = EqConstraint
    val  Eq = EqConstraint
    def loop(constraints: List[Eq]): Map[Name, Type] = constraints match {
      case Nil =>
        Map.empty

      case Eq(σ : ∀, τ : ∀) :: others =>
        // TODO 
        ???

      case Eq(σ1 → τ1, σ2 → τ2) :: others =>
        loop(Eq(σ1, σ2) :: Eq(τ1, τ2) :: others)

      case Eq(★(f1, τ1), ★(f2, τ2)) :: others =>
        loop(Eq(f1, f2) :: Eq(τ1, τ2) :: others)

      case Eq(α(name1), α(name2)) :: others if name1 == name2 =>
        loop(others)

      // TODO: VERIFY SUBSTITUTION IS ALLOWD BY `against`
      // COMMIT SUICIDE OTHERWISE
      case Eq(α(name), τ) :: others =>
        val mgs = loop(others map { case Eq(τ1, τ2) =>
          Eq(τ1 substitute (name -> τ), τ2 substitute (name -> τ))
        })
        val new_τ = τ substitute mgs
        if ((mgs contains name) && mgs(name) != new_τ)
          sys error s"Can't unify ${mgs(name)} = ${new_τ}"
        mgs.updated(name, new_τ)

      case Eq(τ, α(name)) :: others =>
        loop(Eq(α(name), τ) :: others)

      case Eq(τ1, τ2) :: others =>
        if (τ1 == τ2) loop(others)
        else sys error "Inconsistent equality constraints"
    }
    loop(constraints)
  }
}

object TestSystemMF extends SystemMF {

  val chooseType: Type = ∀("α")("α" →: "α" →: "α")
  val chooseBody: Type =        "α" →: "α" →: "α"
  val chooseQ = Set("α": Name)

  val idType: Type = ∀("β")("β" →: "β")
  val idBody: Type =        "β" →: "β"
  val idQ = Set("β": Name)

  val instType: Type = ∀("γ")(∀("δ")("δ" →: "γ") →: "γ")
  val instBody: Type =        ∀("δ")("δ" →: "γ") →: "γ"
  val instArg : Type =               "δ" →: "γ"
  val instArgQ = Set("δ": Name)
  val instQ    = Set("γ": Name)

  def main(args: Array[String]) {
    List(chooseType, idType, instType) foreach {_.ensureMinimalQuantification}

    // it shows nicely that we can't do it in 3 steps.
    //println(unifyNames(instArgQ, idQ, instArg, idBody))
  }
}
