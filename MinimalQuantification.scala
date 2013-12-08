import scala.language.implicitConversions

trait MinimalQuantification
extends Types
   with Pretty
   with FreeNames
   with PeeledNormalForm
{
  def minimallyQuantifiedPNF(π : PNF): PNF = π match {
    case FunPNF(_A, σ, τ) =>
      tryToQuantify(_A, FunPNF(Nil,
        minimallyQuantifiedPNF(σ), minimallyQuantifiedPNF(τ)))

    case AppPNF(_A, f, τ) =>
      tryToQuantify(_A, AppPNF(Nil,
        minimallyQuantifiedPNF(f), minimallyQuantifiedPNF(τ)))

    case VarPNF(_A, x) =>
      tryToQuantify(_A, VarPNF(Nil, x))
  }

  def tryToQuantify(q: Name, π : PNF): PNF =
    if (π doesNotBind q) π else π match {
      case FunPNF(_A, FunPNF(_B, ρ, σ), τ)
          if (τ doesNotBind q) && (σ doesNotBind q) =>
        FunPNF(_A, FunPNF(_B, tryToQuantify(q, ρ), σ), τ)

      case FunPNF(_A, σ, τ)
          if (σ doesNotBind q) =>
        FunPNF(_A, σ, tryToQuantify(q, τ))

      case _ =>
        π adjustQuantifiers (q :: _)
    }

  def tryToQuantify(qs: List[Name], π : PNF): PNF =
    qs.foldRight(π)(tryToQuantify)

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

  implicit class MinimallyQuantifiedTypeOps(τ : Type) {
    def isMinimallyQuantified: Boolean =
      τ.hasWellFormedTypeApps && τ == τ.quantifyMinimally

    def hasWellFormedTypeApps: Boolean = (new TypeAppsAreWellFormed)(τ)

    def ensureMinimalQuantification: Type =
      if (! isMinimallyQuantified)
        sys error s"Not minimally quantified: ${pretty(τ)}"
      else
        τ

    def quantifyMinimally: Type = minimallyQuantifiedPNF(τ.toPNF).toType
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

trait PeeledNormalForm extends PeelAwayQuantifiers {
  private[this] type QList = List[Name]

  trait PNF {
    def quantifiers: QList

    def doesNotBind(q: Name): Boolean = ! (freeNames contains q)

    def adjustQuantifiers(f: QList => QList): PNF = this match {
      case FunPNF(qs, domain, range)    => FunPNF(f(qs), domain, range)
      case AppPNF(qs, typeFun, typeArg) => AppPNF(f(qs), typeFun, typeArg)
      case VarPNF(qs, name)             => VarPNF(f(qs), name)
    }

    def toType: Type = this match {
      case FunPNF(qs, dom, rng) => ∀(qs)(dom.toType →: rng.toType)
      case AppPNF(qs, fun, arg) => ∀(qs)(fun.toType ₌  arg.toType)
      case VarPNF(qs, x)        => ∀(qs)(α(x))
    }

    lazy val freeNames: Set[Name] = this match {
      case FunPNF(qs, domain, range) =>
        domain.freeNames ++ range.freeNames -- qs

      case AppPNF(qs, typeFun, typeArg) =>
        typeFun.freeNames ++ typeArg.freeNames -- qs

      case VarPNF(qs, name) =>
        Set(name) -- qs
    }
  }

  case class FunPNF(quantifiers: QList, domain: PNF, range: PNF) extends PNF
  case class AppPNF(quantifiers: QList, typeFun: PNF, typeArg: PNF) extends PNF
  case class VarPNF(quantifiers: QList, name: Name) extends PNF

  implicit class peeledNormalForm(τ : Type) {
    def toPNF: PNF = τ match {
      case ∀(_, _) =>
        val (quantifiers, body) = listOfQuantifiers(τ)
        body match {
          case σ0 → σ1 => FunPNF(quantifiers, σ0.toPNF, σ1.toPNF)
          case ★(f, a) => AppPNF(quantifiers, f.toPNF, a.toPNF)
          case α(x)    => VarPNF(quantifiers, x)
        }

      case σ0 → σ1 => FunPNF(Nil, σ0.toPNF, σ1.toPNF)
      case ★(f, a) => AppPNF(Nil, f.toPNF, a.toPNF)
      case α(x)    => VarPNF(Nil, x)
    }
  }
}

object TestMinimalQuantification extends MinimalQuantification with Pretty {
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
      false -> ∀("α")("α" →: "α") ₌ "β",
      false -> ∀("α", "β")((("α" →: "α") →: "β") →: "β")
    )
    types foreach { case (mqHood, τ) =>
      val yeah = if (mqHood) "Yeah!" else "Nope!"
      if (mqHood != τ.isMinimallyQuantified) {
        sys error s"Misjudgement! expect $yeah of ${pretty(τ)}"
      }
      if (mqHood)
        println(s"${pretty(τ)}   is minimally quantified.")
      else if (τ.hasWellFormedTypeApps)
        println(s"${pretty(τ)}   becomes   ${pretty(τ.quantifyMinimally)}")
      else
        println(s"${pretty(τ)}   has ill-formed type apps.")
    }
  }
}
