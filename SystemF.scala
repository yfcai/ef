trait SystemMF
extends TypedTerms with MinimalQuantification with Substitution
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

  /** Establish injective correspondence from source to target names */
  def unifyNames(source: Set[Name], target: Set[Name], σ : Type, τ : Type):
      Map[Name, Name] = {
    type T = Map[Name, Name]
    require((source & target).isEmpty)

    def merge(lhs: T, rhs: T): T = {
      lhs.foldRight(rhs) { case ((key, value), acc) =>
        if (acc contains key) {
          val value2 = acc(key)
          if (value == value2)
            acc
          else
            sys error s"merge conflict: $key = $value and $value2"
        }
        else
          acc.updated(key, value)
      }
    }

    case class ID(index: Int) extends IDNumber
    val name = new GenerativeNameGenerator(ID)

    val forbiddens = collection.mutable.Set.empty[Name]

    def loop(σ : Type, τ : Type): T = (σ, τ) match {
      case (∀(name1, body1), ∀(name2, body2)) =>
        val newName = name.next
        loop(body1 rename (name1 -> newName),
             body2 rename (name2 -> newName))

      case (σ1 → τ1, σ2 → τ2) =>
        merge(loop(σ1, σ2), loop(τ1, τ2))

      case (★(f1, σ1), ★(f2, σ2)) =>
        merge(loop(f1, f2), loop(σ1, σ2))

      case (α(a1), α(a2)) if a1 == a2 =>
        Map.empty

      case (α(a1), α(a2)) if a1 != a2 =>
        if ((source contains a1) && (target contains a2))
          Map(a1 -> a2)
        else if ((source contains a2) && (target contains a1))
          Map(a2 -> a1)
        else
          sys error s"irreconcilable names: $a1 and $a2"

      case (α(a1), τ2) =>
        if (source contains a1)
          sys error s"source name ${a1} matches nontarget ${τ2}"
        else {
          if (target contains a1) forbiddens += a1
          Map.empty
        }

      case (τ1, α(a2)) =>
        loop(α(a2), τ1)

      case _ =>
        sys error s"irreconcilable types: ${σ} and ${τ}"
    }

    val result = loop(σ, τ)

    val valueSet: Set[Name] = result.map({
      case (key, value) => value
    })(collection.breakOut)

    if (! (valueSet & forbiddens).isEmpty)
      sys error s"forbidden names used: ${valueSet & forbiddens}"

    if (result.keySet != source)
      sys error s"""|unsettled names: ${source -- result.keySet}
                    |extraneous names: ${result.keySet -- source}""".
                    stripMargin
    result
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
