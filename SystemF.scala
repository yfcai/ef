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
}

trait PeelAwayQuantifiers extends Types {
  def peelAwayQuantifiers(τ : Type): (Set[Name], Type) = τ match {
    case ∀(name, body) =>
      val (otherQuantifiedNames, realBody) = peelAwayQuantifiers(body)
      if (otherQuantifiedNames contains name)
        sys error s"found nonminimally quantified type $τ"
      (otherQuantifiedNames + name, realBody)

    case _ =>
      (Set.empty[Name], τ)
  }
}

trait MostGeneralSubstitution
extends Substitution
   with PeelAwayQuantifiers
{
  case class EqConstraint(lhs: Type, rhs: Type)

  def mostGeneralSubstitution(
    constraints: List[EqConstraint]
  ): Map[Name, Type] = {
    val everythingAllowed = constraints.foldRight(Set.empty[Name]) {
      case (EqConstraint(lhs, rhs), acc) =>
        acc ++ getFreeNames(lhs) ++ getFreeNames(rhs)
    }
    mostGeneralSubstitution(constraints, everythingAllowed)
  }

  def mostGeneralSubstitution(
    constraints: List[EqConstraint],
    replaceable: Set[Name]
  ): Map[Name, Type] =
  {
    type Eq = EqConstraint
    val  Eq = EqConstraint
    case class MGSID(index: Int) extends SecretLocalName
    case class AreBijective(preimage: Set[Name], image: Set[Name])
    val nameGenerator = new GenerativeNameGenerator(MGSID)
    val bijectionConstraints =
      collection.mutable.Stack.empty[(AreBijective, Type, Type)]
    val currentlyReplaceable: collection.mutable.Set[Name] =
      replaceable.map(x => x)(collection.breakOut)
    def loop(constraints: List[Eq]): Map[Name, Type] = constraints match {
      case Nil =>
        Map.empty

      case Eq(σ : ∀, τ : ∀) :: others =>
        val (names1, body1) = peelAwayQuantifiers(σ)
        val (names2, body2) = peelAwayQuantifiers(τ)
        if (names1.size != names2.size)
          sys error s"can't unify unevenly quantified types $σ = $τ"
        val newNames1 = names1 map (_ => nameGenerator.next)
        val newNames2 = names2 map (_ => nameGenerator.next)
        def createRenaming(oldie: Set[Name], newbie: Set[Name]):
            Map[Name, Type] =
          (oldie, newbie).zipped.map({
            case (oldName, newName) => (oldName, α(newName))
          })(collection.breakOut)

        val newEqConstraint = EqConstraint(
          body1 rename createRenaming(names1, newNames1),
          body2 rename createRenaming(names2, newNames2)
        )
        bijectionConstraints.push(
          (AreBijective(newNames1, newNames2), σ, τ)
        )
        currentlyReplaceable ++= newNames1

        loop(newEqConstraint :: others)

      case Eq(σ1 → τ1, σ2 → τ2) :: others =>
        loop(Eq(σ1, σ2) :: Eq(τ1, τ2) :: others)

      case Eq(★(f1, τ1), ★(f2, τ2)) :: others =>
        loop(Eq(f1, f2) :: Eq(τ1, τ2) :: others)

      case Eq(α(name1), α(name2)) :: others if name1 == name2 =>
        loop(others)

      case Eq(α(name1), α(name2)) :: others
          if ! (currentlyReplaceable contains name1) &&
             ! (currentlyReplaceable contains name2) =>
        sys error s"can't unify rigid names $name1 = $name2"

      case Eq(α(name), τ) :: others
          if currentlyReplaceable contains name =>
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
    val result = loop(constraints)

    def verifyBijection(f: Map[Name, Type]):
        ((AreBijective, Type, Type)) => Unit = {
      case (AreBijective(preimage, image), σ, τ) =>
        // keyNotFound means σ is not minimally quantified
        val image0 = preimage map f
        val image1 = image map α
        if (image0 != image1)
          sys error s"can't unify $σ = $τ"
    }
    bijectionConstraints foreach verifyBijection(result)

    val finalResult = result filter (replaceable contains _._1)

    // make sure that finalResult contains no made-up names
    for {
      (_, newType) <- finalResult
      freeNames = getFreeNames(newType)
      (AreBijective(preimage, image), σ, τ) <- bijectionConstraints
    } {
      val badNames = (freeNames & preimage) ++ (freeNames & image)
      if (! badNames.isEmpty)
        sys error s"we were wrong about $σ = $τ"
    }

    finalResult
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

    // Map()
    println(mostGeneralSubstitution(
      EqConstraint(∀("α", "β")("α" →: "β"), ∀("γ", "δ")("δ" →: "γ")) :: Nil
    ))

    // found nonminimally quantified type ∀(α,∀(α,→(α(α),α(α))))
    try { println(mostGeneralSubstitution(
      EqConstraint(∀("α", "α")("α" →: "α"), ∀("γ", "δ")("δ" →: "γ")) :: Nil
    )) } catch { case e: Throwable => println(e.getMessage()) }

    // can't unify rigid names ?2 = ?3
    try { println(mostGeneralSubstitution(
      EqConstraint(∀("α", "β")("α" →: "α"), ∀("γ", "δ")("δ" →: "γ")) :: Nil
    )) } catch { case e: Throwable => println(e.getMessage()) }

    // can't unify ∀(α,∀(β,→(α(α),α(β)))) = ∀(γ,∀(δ,→(α(δ),α(δ))))
    try { println(mostGeneralSubstitution(
      EqConstraint(∀("α", "β")("α" →: "β"), ∀("γ", "δ")("δ" →: "δ")) :: Nil
    )) } catch { case e: Throwable => println(e.getMessage()) }

    // key not found (means lhs type is not minimally quantified)
    try { println(mostGeneralSubstitution(
      EqConstraint(
        ∀("α", "β")("α" →: "γ"), ∀("γ", "δ")("γ" →: "δ")) :: Nil
    )) } catch { case e: Throwable => println(e.getMessage()) }

    // we were wrong about ∀(α,→(α(α),α(γ))) = ∀(γ,→(α(γ),α(γ)))
    try { println(mostGeneralSubstitution(
      EqConstraint(∀("α")("α" →: "γ"), ∀("γ")("γ" →: "γ")) :: Nil
    )) } catch { case e: Throwable => println(e.getMessage()) }

    // Map(γ -> ★(α(List),α(δ)))
    println(mostGeneralSubstitution(
      EqConstraint(∀("α")("α" →: "γ"), ∀("γ")("γ" →: ★("List", "δ"))) :: Nil
    ))
  }
}
