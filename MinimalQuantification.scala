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
    def quantifyMinimally(quantified: Set[Name], τ : Type): Type =
      tryToQuantify(quantified.toList, τ.toPNF).toType
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

    def renameAll(f0: Map[Name, Name]): PNF = {
      val f = f0 withDefault identity
      def loop(π : PNF): PNF = π match {
        case FunPNF(qs, dom, rng) => FunPNF(qs map f, loop(dom), loop(rng))
        case AppPNF(qs, fun, arg) => AppPNF(qs map f, loop(fun), loop(arg))
        case VarPNF(qs, name)     => VarPNF(qs map f, f(name))
      }
      loop(this)
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

trait PrenexForm extends PeeledNormalForm {
  case class PrenexType(forall: List[Name], exists: List[Name], π : PNF) {
    def toType: Type =
      if (exists.isEmpty)
        ∀(forall)(π.toType)
      else π match {
        case FunPNF(Nil, dom, rng) =>
          ∀(forall)(∀(exists)(dom.toType) →: rng.toType)
      }
  }

  def prenexPNF(π : PNF): PrenexType = π match {
    case FunPNF(_A, σ0, τ0) =>
      val PrenexType(forall_σ, exists_σ, σ) = prenexPNF(σ0)
      val PrenexType(forall_τ, exists_τ, τ) = prenexPNF(τ0)
      val (qs_σ, qs_τ) = (forall_σ ++ exists_σ, forall_τ ++ exists_τ)
      val freeNames = σ0.freeNames ++ τ0.freeNames
      val freshNames = getFreshNames(qs_σ ++ qs_τ, freeNames)
      val (fresh_σ, fresh_τ) = freshNames splitAt qs_σ.length
      val subst_σ = (Map.empty[Name, Name] ++ (qs_σ, fresh_σ).zipped).
        withDefault(identity)
      val subst_τ = (Map.empty[Name, Name] ++ (qs_τ, fresh_τ).zipped).
        withDefault(identity)
      PrenexType(
        _A ++ (exists_σ map subst_σ) ++ (forall_τ map subst_τ),
              (forall_σ map subst_σ) ++ (exists_τ map subst_τ),
        FunPNF(Nil, (σ renameAll subst_σ), (τ renameAll subst_τ))
      )

    case AppPNF(qs, fun, arg) =>
      PrenexType(qs, Nil, AppPNF(Nil, fun, arg))

    case VarPNF(qs, x) =>
      PrenexType(qs, Nil, VarPNF(Nil, x))
  }

  implicit class PrenexNormalFormOps(τ : Type) {
    def toPrenex: Type = prenexPNF(τ.toPNF).toType
  }
}

object TestMinimalQuantification
extends MinimalQuantification
   with PrenexForm
   with Pretty
{
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
      false -> ∀("α", "β")((("α" →: "α") →: "β") →: "β"),
      false -> (∀("α", "β")((("α" →: "α") →: "β") →: "β") →: "η") →: "ζ"
    )
    types foreach { case (mqHood, τ) =>
      val yeah = if (mqHood) "Yeah!" else "Nope!"
      if (mqHood != τ.isMinimallyQuantified) {
        sys error s"Misjudgement! expect $yeah of ${pretty(τ)}"
      }
      val (prenex, mq) = (τ.toPrenex, τ.quantifyMinimally)
      println(pretty(prenex))
      if (prenex != mq) println(pretty(mq))
      println()
    }
  }
}
