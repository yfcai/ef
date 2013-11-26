trait MinimalQuantification extends Types with FreeNames with Pretty {
  // domain M = name -> is free in a good way or a bad way
  // FYI, true is good, false is bad.
  private[this] type M = Map[Name, Boolean]

  private sealed trait MQ {
    def >>= (f: M => MQ): MQ
  }

  private case object NotMQ extends MQ {
    def >>= (f: M => MQ): MQ = NotMQ
  }

  private case class Solo(goodAndBad: M) extends MQ {
    def >>= (f: M => MQ): MQ = f(goodAndBad)
  }

  private case class Duo(lhs: M, rhs: M) extends MQ {
    def >>= (f: M => MQ): MQ = f(merge(lhs, rhs))
  }

  private def merge(lhs: M, rhs: M): M =
    (lhs map { case (name, goodness) =>
      if (rhs contains name)
        (name, goodness && rhs(name))
      else
        (name, goodness)
    }) ++ rhs.filter(p => ! (lhs contains p._1))

  private class IsMinimallyQuantified extends TypeVisitor[MQ] {
    private[this] type T = MQ

    def ∀(name: Name, body: T): T = body match {
      case Duo(lhs, rhs)
          if lhs.getOrElse(name, false) &&
             rhs.getOrElse(name, true ) =>
        Duo(lhs - name, rhs - name)

      case Solo(goodAndBad)
          if goodAndBad.getOrElse(name, false) =>
        Solo(goodAndBad - name)

      case _ =>
        NotMQ
    }

    def →(domain: T, range: T): T =
      domain >>= { domain =>
      range  >>= { range  =>
      Duo(domain, range) }}

    def α(name: Name): T = Solo(Map(name -> true))

    def ★(typeFun: T, typeArg: T) =
      typeFun >>= { typeFun =>
      typeArg >>= { typeArg =>
      Solo(typeArg ++ (typeFun mapValues (! _))) }}
  }

  // All subtree of the type should be in head normal form.
  def noComplicatedTypeApplication: Type => Boolean = { τ =>
    def f = noComplicatedTypeApplication
    τ match {
      case ∀(name, body)    => f(body)
      case →(domain, range) => f(domain) && f(range)
      case α(name)          => true

      case ★(typeFun: ★, typeArg) => f(typeFun) && f(typeArg)
      case ★(α(_), typeArg)       => f(typeArg)
      case ★(_, _)                => false
    }
  }

  implicit class MinimallyQuantifiedTypeOps(τ : Type) {
    def isMinimallyQuantified: Boolean =
      noComplicatedTypeApplication(τ) &&
      NotMQ != (new IsMinimallyQuantified)(τ)

    def ensureMinimalQuantification: Type =
      if (! isMinimallyQuantified)
        sys error s"Not minimally quantified: ${pretty(τ)}"
      else
        τ
  }

  implicit class MinimallyQuantifyingNameOps(quantified: Set[Name]) {
    def quantifyMinimallyOver(τ : Type): Type =
      quantifyMinimally(quantified, τ)

    private[this]
    def quantifyMinimally(quantified: Set[Name], τ : Type): Type = τ match {
      case ∀(name, body) =>
        ∀(name, quantifyMinimally(quantified - name, body))

      case ★(f, α) =>
        val freeNames = getFreeNames(f) ++ getFreeNames(α)
        ∀(freeNames & quantified)(★(f, α))

      case σ → τ =>
        val freeNames = getFreeNames(σ)
        ∀(freeNames & quantified)(σ →:
            quantifyMinimally(quantified -- freeNames, τ))

      case α(name) =>
        if (quantified contains name)
          ∀(name, α(name))
        else
          α(name)
    }
  }
}

object TestMinimalQuantification extends MinimalQuantification {
  def main(args: Array[String]) {
    val types = List(
      true  -> ∀("α")("α" →: "α"),
      true  -> ∀("α", "β")(("α" →: "β") →: ("List" ₌ "α") →: ("List" ₌ "β")),
      true  -> "List" ₌ ("List" ₌ "α"),
      true  -> "Map" ₌ ("List" ₌ "α") ₌ ("Map" ₌ "α" ₌ "β"),
      true  -> ∀("α")("α"),
      true  -> ∀("α")("List" ₌ "α"),
      true  -> ∀("α")("α" →: "β"),
      true  -> ∀("α")("α") →: "β",
      false -> ∀("β")("α" →: "β"),
      false -> ("α" →: "β") ₌ "γ",
      false -> ∀("α")("α" →: "α") ₌ "β"
    )
    types foreach { case (mqHood, τ) =>
      val yeah = if (mqHood) "Yeah!" else "Nope!"
      if (mqHood != τ.isMinimallyQuantified) {
        sys error s"Misjudgement! expect $yeah of ${pretty(τ)}"
      }
      println("%s %s".format(yeah, pretty(τ)))
    }
  }
}

