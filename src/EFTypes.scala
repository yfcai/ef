trait Unification extends Syntax with PrenexForm {
  case class ≡(lhs: Type, rhs: Type) {
    override def toString = s"${lhs.unparse}  ≡  ${rhs.unparse}"
  }
  implicit class makeEqualityConstraint(lhs: Type) {
    def ≡(rhs: Type) = new ≡(lhs, rhs)
  }

  private type DegreeOfFreedom = List[α]

  private def err(message: String, constraints: List[≡]) =
    sys error s"$message:\n${constraints.head}"

  def resolveConstraints(dog: DegreeOfFreedom, constraints: ≡ *):
      Map[α, Type] =
  {
    type TypeEnv = Map[Type.Binder, Type]
    def loop(constraints: List[≡]): TypeEnv = constraints match {
      case (σ1 → τ1) ≡ (σ2 → τ2) :: rest =>
        loop(σ1 ≡ σ2 :: τ1 ≡ τ2 :: rest)

      case (σ1 ₌ τ1) ≡ (σ2 ₌ τ2) :: rest =>
        loop(σ1 ≡ σ2 :: τ1 ≡ τ2 :: rest)

      case δ(a1) ≡ δ(a2) :: rest if a1 == a2 =>
        loop(rest)

      case (a: α) ≡ τ :: rest =>
        if (dog contains a) {
          val mgs = loop(rest map {
            case lhs ≡ rhs => (lhs subst (a, τ)) ≡ (rhs subst (a, τ))
          })
          mgs updated (a.binder, τ subst mgs)
        }
        else err("trying to unify rigid type variable", constraints)

      case τ ≡ (a: α) :: rest =>
        loop(a ≡ τ :: rest)

      case Nil =>
        Map.empty

      // error cases
      case (_: Type.Binder) ≡ _ :: _ | _ ≡ (_: Type.Binder) :: _ =>
        err("can't unify quantified types yet", constraints)

      case _ =>
        err("Inconsistent constraint", constraints)
    }
    loop(constraints.toList) map { case (binder, τ) => (α(binder), τ) }
  }
}

trait PrenexForm extends Types {
  case class PrenexForm(all : List[α], ex : List[α], τ: Type) {
    def addUniversal(x: Type.Binder) = {
      val a = α(x)
      PrenexForm(a :: all, ex, τ)
    }

    def addExistential(x: Type.Binder) = {
      val a = α(x)
      PrenexForm(all, a :: ex, τ)
    }

    def toType: Type =
      all.foldRight(
        ex.foldRight(τ) {
          case (a, τ) => ∃(a.binder.name) { b => τ subst (a.binder, b) }
        }
      ) {
        case (a, τ) => ∀(a.binder.name) { b => τ subst (a.binder, b) }
      }
  }

  object PrenexForm {
    def apply(τ: Type): PrenexForm = τ match {
      case ∀(a, body) =>
        PrenexForm(body) addUniversal   a
      case ∃(a, body) =>
        PrenexForm(body) addExistential a
      case σ → τ =>
        val (ps, pt) = (PrenexForm(σ), PrenexForm(τ))
        PrenexForm(ps.ex ++ pt.all, ps.all ++ pt.ex, ps.τ →: pt.τ)
      case _ =>
        PrenexForm(Nil, Nil, τ)
    }
  }
}

trait EFTypes extends Gamma with Unification {
}
