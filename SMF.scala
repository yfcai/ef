trait SystemMF
extends TypedTerms
   with PrenexForm
   with MinimalQuantification
   with MostGeneralSubstitution
{
  case class SMFTerm(
    canon      : Term,
    Γ          : PartialFunction[Name, Type],
    globalTypes: Set[Name],
    names      : Map[Name, Name]
  )
  extends TypedTerm {
    lazy val getTerm: Term = canon renameAll names

    lazy val getType: Type = typeOfSubterm(canon, globalTypes)

    // TODO: Cache me to speed up typing, maybe... but how?
    def typeOfSubterm(subterm: Term, boundTypeVars: Set[Name]): Type = {
      case class ID(index: Int) extends SecretLocalName
      val nameGenerator = new GenerativeNameGenerator(ID)

      def loop(t : Term, boundTypeVars : Set[Name]): Type =
      {
        t match {
          case χ(name) =>
            Γ(name)

          case λ(name, body) =>
            val σ = Γ(name)
            val quantifiedNames = getFreeNames(σ) -- boundTypeVars
            val τ = loop(body, boundTypeVars ++ quantifiedNames)
            ∀(quantifiedNames)(σ →: τ)

          case ε(operator, operand) =>
            val operatorType = loop(operator, boundTypeVars)
            val operandType  = loop(operand , boundTypeVars)
            val (setB, innerOperatorType) = peelAwayQuantifiers(operatorType)
            innerOperatorType match {
              case α(name) if setB == Set(name) =>
                ∀(name, α(name))
                // If operator type is ∀α. α, then we should allow
                // the application into false. All other legal cases
                // are covered below.

              case _ =>
                val Prenex(f_∀, f_∃, sigma0 → tau0) = operatorType.toPrenex
                val Prenex(x_∀, x_∃, sigma1       ) = operandType.toPrenex
                val List((fA, fAsub), (fE, fEsub), (xA, xAsub), (xE, xEsub)) =
                  List(f_∀, f_∃, x_∀, x_∃) map {
                    set => getReplacement(set, nameGenerator)
                  }
                val σ0 = sigma0 rename (fAsub ++ fEsub)
                val σ1 = sigma1 rename (xAsub ++ xEsub)
                val MGS4App(mgs, survivors, existentialMap) =
                  getMGS4App(fE ++ xE, fA ++ xA, σ0, σ1,
                    fEsub.inverse ++ xEsub.inverse)
                val τ  = tau0 rename (fAsub ++ fEsub) substitute mgs
                val existentials = existentialMap.keySet.toList
                // just test outer level & partition surviving existentials
                // maybe it will break if you unify to nested inner
                // existentials that should have been turned into
                // universals?
                val (outerE, innerE) = if (τ.isInstanceOf[→]) {
                  val (τ0 → τ1) = τ
                  val free = getFreeNames(τ1)
                  existentials partition (free contains _)
                } else (existentials, Nil)
                val freeNames_τ = getFreeNames(τ)
                // Get back original names
                val (invBC, _) =
                  (xAsub.inverse ++ fAsub.inverse ++
                    xEsub.inverse ++ fEsub.inverse).foldRight(
                    Map.empty[Name, Name],
                    freeNames_τ) {
                  case ((idC, nameC), (acc, toAvoid)) =>
                    val newNameC = getFreshName(nameC, toAvoid)
                    (acc.updated(idC, newNameC), toAvoid + newNameC)
                }
                val invSub: Map[Name, Type] = invBC map {
                  case (id, name) => (id, α(name))
                }
                val new_τ = if (innerE.isEmpty) τ else {
                  val (τ0 → τ1) = τ
                  (∀(innerE map invBC)(τ0 substitute invSub).
                    quantifyMinimally) →: τ1
                }
                val resultType =
                  ((survivors ++ outerE) map invBC).
                    quantifyMinimallyOver(new_τ substitute invSub)
                resultType
            }
        }
      }
      loop(subterm, boundTypeVars)
    }
  }

  def getReplacement(source: Set[Name],
                     nameGenerator: GenerativeNameGenerator):
      (Set[Name], Map[Name, Name]) = {
    val names = source map (_ => nameGenerator.next)
    val renaming: Map[Name, Name] = (source, names).zipped.map({
      case (oldName, newName) => (oldName, newName)
    })(collection.breakOut)
    (names, renaming)
  }

  /** @param forbidden   vestigal, to remove */
  case class MGS4App(typeAppsB: Map[Name, Type],
                     survivors: Set[Name],
                     forbidden: Map[Name, Name])

  /** Unify σ0 and σ1 such that A is unified to a subset of B
    * that is used nowhere else. */
  def getMGS4App(A: Set[Name], B: Set[Name],
                σ0: Type, σ1: Type,
                oldA: Name => Name = {x => x}):
      MGS4App =
  {
    val Eq  = EqConstraint
    val mgs = mostGeneralSubstitution(List(Eq(σ0, σ1)), B)
    val newMgs: Iterable[(Name, Type)] = for {
      (a, τ) <- mgs
      freeNames = getFreeNames(τ)
      s = freeNames & A
      if s.isEmpty || (! τ.isInstanceOf[α])
    } yield {
      if (s.isEmpty)
        (a, τ)
      else {
        var toAvoid = freeNames
        val newNames: Map[Name, Name] = s.map(b => {
          val fresh = getFreshName(oldA(b), toAvoid)
          toAvoid = toAvoid + fresh
          (b, fresh)
        })(collection.breakOut)
        // If τ is a function and s isn't free in the result type,
        // then quantify s existentially. Otherwise quantify s
        // universally.
        //
        // I've no idea why this actually works.
        val default = (a, ∀(s map newNames)(τ rename newNames))
        if (τ.isInstanceOf[→]) {
          val (τ0 → τ1) = τ
          if ((getFreeNames(τ1) & s).isEmpty)
            (a, ∀(s map newNames)(τ0 rename newNames) →: τ1)
          else
            default
        }
        else
          default
      }
    }
    MGS4App(Map.empty[Name, Type] ++ newMgs,
            B -- mgs.keySet,
            Map.empty[Name, Name] ++ (A, A).zipped
           /* vestigal param reappropriated to save existentials */)
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

  /** @param τ Type to inspect
    * @param n Maximum number of quantified names to return
    * @return (list-of-quantified-names, the-rest-of-τ)
    */
  def listOfQuantifiers(τ : Type, n: Int = -1):
      (List[Name], Type) = τ match {
    case ∀(name, body) if n != 0 =>
      val (otherQuantifiedNames, realBody) =
        listOfQuantifiers(body, if (n > 0) n - 1 else n)
      (name :: otherQuantifiedNames, realBody)

    case _ if n > 0 =>
      sys error s"Too many type arguments for ${τ}"

    case _ =>
      (Nil, τ)
  }

  /** Suppose
    *
    *   τ = ∀α β. α → (∀γ. (∀δ. δ → γ) → β → α)
    *
    * then
    *
    *   argumentQuantificationList(τ) =
    *     ( {α, β}, α         ) ::
    *     (    {γ}, ∀δ. δ → γ ) ::
    *     (      ∅, β         ) ::
    *     (      ∅, α         ) :: Nil
    */
  def argumentQuantificationList(τ : Type): List[(Seq[Name], Type)] = {
    def loop(τ : Type, currentQuantifiers: Seq[Name]):
        List[(Seq[Name], Type)] = τ match {
      case ∀(alpha, body) =>
        loop(body, currentQuantifiers :+ alpha)

      case σ → τ =>
        (currentQuantifiers, σ) :: loop(τ, Seq.empty)

      case nonfunctionType =>
        (currentQuantifiers, nonfunctionType) :: Nil
    }
    loop(τ, Seq.empty)
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

trait SystemMFExamples extends SystemMF {

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

  val chooseId =
    SMFTerm("choose" ₋ "id",
            Map(StringLiteral("choose") -> chooseType,
                StringLiteral("id")     -> idType),
            Set.empty,
            Map.empty)

  val chooseIdId =
    SMFTerm(chooseId.getTerm ₋ "id", chooseId.Γ, Set.empty, Map.empty)

  val undefinedUndefined =
    SMFTerm("undefined" ₋ "undefined",
            Map(StringLiteral("undefined") -> ∀("α")("α")),
            Set.empty,
            Map.empty)

  val constUndefined =
    SMFTerm("const" ₋ "undefined",
            Map(StringLiteral("const") -> ∀("α")("α" →: ∀("β")("β" →: "α")),
                StringLiteral("undefined") -> ∀("α")("α")),
            Set.empty,
            Map.empty)

  val constId =
    SMFTerm("const" ₋ "id",
            Map(StringLiteral("const") -> ∀("α")("α" →: ∀("β")("β" →: "α")),
                StringLiteral("id") -> idType),
            Set.empty,
            Map.empty)

  val const2Id =
    SMFTerm("const2" ₋ "id",
            Map(StringLiteral("const2") -> ∀("α")("α" →: "β" →: "α"),
                StringLiteral("id") -> idType),
            Set("β": Name),
            Map.empty)

  val selfApp =
    SMFTerm(λ("x")("x" ₋ "x"),
            Map(StringLiteral("x") -> idType),
            Set.empty,
            Map.empty)

  val selfAppId =
    SMFTerm(selfApp.canon ₋ λ("y")("y"),
            selfApp.Γ orElse Map(StringLiteral("y") -> α("β")),
            Set.empty,
            Map.empty)

  val listOfSystemMFExamples: List[SMFTerm] =
    List(chooseId, chooseIdId, undefinedUndefined, constUndefined,
         constId, const2Id, selfApp, selfAppId)
}

object TestSystemMF extends SystemMFExamples {
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

    // type soundness issue
    // make sure precondition is met (global environment contains
    // only values of minimally quantified types)
    constUndefined.Γ.asInstanceOf[Map[Name, Type]].foreach {
      case (name, theType) => theType.ensureMinimalQuantification
    }
    // test that the result type of application is still minimally
    // quantified
    constUndefined.getType.ensureMinimalQuantification

    listOfSystemMFExamples foreach {
      example => println() ; println(pretty(example))
    }
  }
}

object TypeChecker extends FileParser with Pretty {
  def process(result: List[Expr]): Unit = result foreach {
    case DefExpr(name, term) =>
      println(s"$name : ${pretty(term.getType)}")
      println(s"$name = ${pretty(term.getTerm)}")
      println()

    case NakedExpr(term) =>
      println(pretty(term))
      println()
  }
}
