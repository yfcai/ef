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

  // given mgs and two prenexes (for quantifiers only),
  // produce:
  //
  //     (universal survivors, existential survivors, modified mgs)
  //
  def classifyMGS(mgs: Map[α, Type], lhs: PrenexForm, rhs: PrenexForm):
      (Set[α], Set[α], Map[α, Type]) = {
    import UnificationHelpers._
    val all = collection.mutable.Set.empty[α] ++ lhs.all ++ rhs.all
    val ex  = collection.mutable.Set.empty[α] ++ lhs.ex  ++ rhs.ex
    val either = all ++ ex
    def err(msg: String) = sys error (
      "\n$msg in:\nfun : ${lhs.toType.unparse}" +
                "\narg : ${rhs.toType.unparse}"
    )
    val modifiedMGS: Map[α, Type] = mgs map { case (a, τ) =>
      all -= a
      τ match {
        // universal unified to universal, do nothing, or:
        // universal unified to existential, do nothing beyond
        // the deletion of the universal, which is already done
        case b: α if either contains b =>
          (a, b)

        // unified to something not bound here, freak out
        case b: α =>
          err(s"$a unified to out-of-scope name $b")

        // universal unified to a nontrivial type, tons of work
        case τ0 =>
          val τ = (ex & unbound(τ0)).foldRight(τ0) {
            case (e, τ) =>
              // any existential in a nontrivial type unified to
              // a universal cannot appear anywhere outside.
              ex -= e
              // make sure that e appears nowhere else
              if (count(e, τ0) != count(e, lhs.τ, rhs.τ))
                err(s"the existential $e in ${τ0.unparse} escaped!")
              // compute depth (number of greatest nesting to the
              // left of function arrows)
              val depthInside  = depth(e, τ0)
              val depthOutside = depth(e, lhs.τ, rhs.τ)
              assert(depthInside >= 0 && depthOutside >= 0)
              // if depth parities are equal inside & out,
              // quantify e existentially; otherwise universally
              if (depthInside % 2 == depthOutside % 2)
                ∃(e.binder.name) { x => τ subst (e, x) }
              else
                ∀(e.binder.name) { x => τ subst (e, x) }
          }
          (a, τ)
      }
    }
    (all.toSet, ex.toSet, modifiedMGS)
  }

  object UnificationHelpers {
    def unbound(τ: Type): Set[α] = {
      import Type._
      τ.fold[Set[α]] {
        case α_(a)          => Set(α(a))
        case b: Π1Binder[_] => b.body - α(b.binder)
        case p: Π2[_]       => p.π1 ++ p.π2
        case _              => Set.empty
      }
    }

    def count(a: α, τ1: Type, τ2: Type): Int =
      count(a, τ1) + count(a, τ2)

    def count(a: α, τ: Type): Int = {
      import Type._
      τ.fold[Int] {
        case α_(b) if α(b) == a => 1
        case b: Π1[_]           => b.π1
        case p: Π2[_]           => p.π1 + p.π2
        case _: Π0[_]           => 0
      }
    }

    // depth: the biggest number of arrows to the right of
    // this variable
    def depth(a: α, τ1: Type, τ2: Type): Int =
      Math.max(depth(a, τ1), depth(a, τ2))

    def depth(a: α, τ: Type): Int = {
      import Type._
      τ.fold[Int] {
        case α_(b) if α(b) == a => 0
        case →:(lhs, rhs)       => Math.max(1 + lhs, rhs)
        case p: Π2[_]           => Math.max(p.π1, p.π2)
        case b: Π1[_]           => b.π1
        case _: Π0[_]           => Int.MinValue // I mean -∞
      }
    }

    // how soon does a appear in τ
    def ordinal(a: α, τ: Type): Int = {
      val i = τ.traverse.indexOf(a)
      if (i < 0) Int.MaxValue /* I mean ∞ */ else i
    }
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
