trait MinimalQuantification
extends Types
   with Pretty
   with FreeNames
   with PeelAwayQuantifiers
{
  /** Test that leaves of a type application tree (★) are legal.
    *
    * ∀ is forbidden to be a left leaf.
    * → is forbidden to be a left leaf.
    * α can be both.
    */
  class TypeAppsAreWellFormed extends TypeVisitor[Boolean] {
    private[this] type T = Boolean

    def ∀(name: Name, body: T): T = body

    def →(domain: T, range: T): T = domain && range

    def ★(typeFun: T, typeArg: T) = typeFun && typeArg

    def α(name: Name): T = true

    override def apply(τ : Type): T = τ match {
      case ★(→(_, _), _)
         | ★(∀(_, _), _) => false

      case _ => super.apply(τ)
    }
  }

  class IsMinimallyQuantified extends TypeVisitor[Boolean] {
    private[this] type T = Boolean

    def ∀(name: Name, body: T): T = sys error "we're not supposed to be here"

    def →(domain: T, range: T): T = domain && range

    def ★(typeFun: T, typeArg: T) = typeFun && typeArg

    def α(name: Name): T = true

    override def apply(τ : Type): T = τ match {
      case forallType @ ∀(_, _) =>
        val (quantifiers, body) = peelAwayQuantifiers(forallType)
        body match {
          case σ → τ =>
            (quantifiers -- getFreeNames(σ)   ).isEmpty && apply(body)

          case _ =>
            (quantifiers -- getFreeNames(body)).isEmpty && apply(body)
        }

      case _ => super.apply(τ)
    }
  }

  implicit class MinimallyQuantifiedTypeOps(τ : Type) {
    def isMinimallyQuantified: Boolean =
      (new TypeAppsAreWellFormed)(τ) && (new IsMinimallyQuantified)(τ)

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
      true  -> ★("Contravariant", ∀("α")("α")),
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
