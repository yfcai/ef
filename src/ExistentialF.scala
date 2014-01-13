/** the type system */
trait ExistentialF extends Unification with Prenex {
  /*

  def resultType(operatorType: Tree, operandType: Tree): Status[Tree] = {
    val Seq(operatorPrenex, operandPrenex) =
      Prenex(operatorType, operandType)
    val prefix = Prefix(operatorPrenex.prefix ++ operandPrenex.prefix)

    // get rid of absurd operators
    resultTypeOfAbsurdOperator(
      prefix, operatorPrenex, operandPrenex
    ) match {
      case None => ()
      case Some(result) => return Success(result)
    }
    // now we can assume operatorPrenex.body to be a function arrow.

    val σ0 → τ = operatorPrenex.body
    val σ1     = operandPrenex.body
    val mgs    = unifyMonotypes(prefix.degreesOfFreedom, σ0, σ1) match {
      case Success(mgs) => mgs
      case Failure(msg) => return Failure(msg)
    }

    // process mgs, dissolving families, selling children
    // 1. collect the debt of families in existential crisis
    val (prefixAfterDebtCollection, mgsAfterDebtCollection) =
      collectDebts(prefix, mgs) match {
        case Success(stuff) => stuff
        case Failure(msg) => return Failure(msg)
      }

    // 2. increase the debt of families in financial crisis
    val prefixAfterLoan =
      issueLoans(prefixAfterDebtCollection, mgsAfterDebtCollection)

    // 3. independent children kill their parents
    val prefixAfterMurder =
      murderParents(prefixAfterLoan, mgsAfterDebtCollection)

    val prefixAfterDissolution = prefixAfterMurder
    val mgsAfterDissolution = mgsAfterDebtCollection

    // after dissolution, each family in the domain of the mgs suffer
    // one of the following fates:
    //
    // 1. a child disappears, family debt is increased
    //
    // 2. an existential family breaks apart, debts are forgiven,
    //    children become free quantifiers without family ties
    //
    // 3. a universal family is dissolved, debts are paid,
    //    all children are killed
    //
    // after all of that, no surviving family member remains in
    // the domain of mgs.

    // TODO: verify in paranoia that σ0 and σ1 are actually unified

    // capture family heads
    //
    // do not deal with family members who may want to become
    // uncertain for now. if the assertion failure waiting to happen
    // did happen, then we have to deal with them.
    val (specsAfterCapture, mgsAfterCapture) =
      captureChildren(
        prefixAfterDissolution,
        mgsAfterDissolution,
        operatorPrenex,
        operandPrenex)

    Success(Prenex.normalize(specsAfterCapture, τ subst mgsAfterCapture))
  }

  def collectDebts(prefix: Prefix, mgs: Map[String, Tree]):
      Status[(Prefix, Map[String, Tree])] = ???

  // borrow against the future
  def issueLoans(prefix: Prefix, mgs: Map[String, Tree]):
      Prefix = prefix // TODO

  def murderParents(prefix: Prefix, mgs: Map[String, Tree]):
      Prefix = prefix // TODO

  def captureChildren(
    prefix: Prefix,
    mgs: Map[String, Tree],
    operatorPrenex: Prenex,
    operandPrenex: Prenex):
      (Seq[PrenexSpec], Map[String, Tree]) = {
    val uncertainties = collection.mutable.Set.empty[String]
    val mgsAfterCapture = mgs.map {
      case (α, τ) =>
        val typeAfterCapture = τ.freeNames.foldRight(τ) {
          // β is captured
          case (β, newType)
              if isCaptured(β, τ, operatorPrenex, operandPrenex) =>

            // freak out if some uncertainties are family members:
            // assertion failure waiting (for an example) to happen.
            // when it does, it is time to revise `bindChild` and
            // `unsettleParent`.
            prefix.tagOf(β) match {
              case UniversalQuantification
                 | ExistentialQuantification => ()
              case tag =>
                sys error s"unexpected tag captured: $tag"
            }

            uncertainties += β

            val sign =
              if (paritiesMatch(β, τ, operatorPrenex, operandPrenex))
                prefix.tagOf(β)
              else
                Prenex.flipTag(prefix.tagOf(β))

            bindChild(sign, β, newType)

          // β is not captured
          case (β, newType) =>
            newType
        }
        (α, typeAfterCapture)
    }

    val specsAfterCapture = prefix.specs.map {
      case spec @ PrenexSpec(tag, β, _*)
          if uncertainties contains β =>
        unsettleParent(spec)

      case otherwise =>
        otherwise
    }

    (specsAfterCapture, mgsAfterCapture)
  }

  // precondition: spec.tag is free universal/existential
  def unsettleParent(spec: PrenexSpec): PrenexSpec = spec.tag match {
    case UniversalQuantification =>
      PrenexSpec(UniversalUncertainty, spec.x, Prenex(Nil, TypeList()))
    case ExistentialQuantification =>
      PrenexSpec(ExistentialUncertainty, spec.x, Prenex(Nil, TypeList()))
  }

  // precondition: sign is universal-/existential-quantification.
  def bindChild(sign: Tag, β: String, body: Tree): Tree = sign match {
    // to understand, consult Experiments.ScopingExperiment
    // (need to change now)
    case UniversalQuantification =>
      ∀=(β, æ(β), body)
    case ExistentialQuantification =>
      ∃=(β, æ(β), body)
  }

  // nice to have monotype τ
  def isCaptured(β: String, τ: Tree, pn1: Prenex, pn2: Prenex): Boolean =
    Prenex.count(β, τ) == pn1.count(β) + pn2.count(β)

  // nice to have monotype τ
  def paritiesMatch(β: String, τ: Tree, pn1: Prenex, pn2: Prenex):
      Boolean = {
    val depthInside  = Prenex.depth(β, τ)
    val depthOutside = Math.max(pn1.depth(β), pn2.depth(β))
    assert(depthInside  >= 0)
    assert(depthOutside >= 0)
    depthInside % 2 == depthOutside % 2
  }

  // an operator type is absurd if its body isn't a function arrow.
  def resultTypeOfAbsurdOperator(
    prefix        : Prefix,
    operatorPrenex: Prenex,
    operandPrenex : Prenex): Option[Tree] = operatorPrenex.body match {
    case σ → τ => None
    case _ => sys error s"TODO: handle absurd operators"
  }

   */
}
