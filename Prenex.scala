trait PrenexForm extends MinimalQuantification with PeeledNormalForm {
  case class Prenex(forall: Set[Name], exists: Set[Name], body: Type)

  case class PrenexPNF(forall: List[Name], exists: List[Name], π : PNF) {
    def toType: Type =
      if (exists.isEmpty)
        ∀(forall)(π.toType)
      else π match {
        case FunPNF(Nil, dom, rng) =>
          ∀(forall)(∀(exists)(dom.toType) →: rng.toType)
      }

    def toMinimallyQuantifiedType: Type = toType.quantifyMinimally
  }

  def prenexPNF(π : PNF): PrenexPNF = π match {
    case FunPNF(_A, σ0, τ0) =>
      val PrenexPNF(forall_σ, exists_σ, σ) = prenexPNF(σ0)
      val PrenexPNF(forall_τ, exists_τ, τ) = prenexPNF(τ0)
      val (qs_σ, qs_τ) = (forall_σ ++ exists_σ, forall_τ ++ exists_τ)
      val freeNames = σ0.freeNames ++ τ0.freeNames
      val freshNames = getFreshNames(qs_σ ++ qs_τ, freeNames)
      val (fresh_σ, fresh_τ) = freshNames splitAt qs_σ.length
      val subst_σ = (Map.empty[Name, Name] ++ (qs_σ, fresh_σ).zipped).
        withDefault(identity)
      val subst_τ = (Map.empty[Name, Name] ++ (qs_τ, fresh_τ).zipped).
        withDefault(identity)
      PrenexPNF(
        _A ++ (exists_σ map subst_σ) ++ (forall_τ map subst_τ),
              (forall_σ map subst_σ) ++ (exists_τ map subst_τ),
        FunPNF(Nil, (σ renameAll subst_σ), (τ renameAll subst_τ))
      )

    case AppPNF(qs, fun, arg) =>
      PrenexPNF(qs, Nil, AppPNF(Nil, fun, arg))

    case VarPNF(qs, x) =>
      PrenexPNF(qs, Nil, VarPNF(Nil, x))
  }

  implicit class PrenexNormalFormOps(τ : Type) {
    def toPrenexType: Type = prenexPNF(τ.toPNF).toType

    def toPrenex: Prenex = {
      val PrenexPNF(forall, exists, π) = prenexPNF(τ.toPNF)
      val (aSet, eSet) = (forall.toSet, exists.toSet)
      assert(aSet.size == forall.size)
      assert(eSet.size == exists.size)
      assert((aSet & eSet).isEmpty)
      Prenex(aSet, eSet, π.toType)
    }
  }
}
