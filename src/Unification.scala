trait Unification extends Syntax with PrenexForm {
  unification =>

  // ERROR HANDLING

  class TypeError(val message: String) extends Exception(message)
  object TypeError {
    def apply(message: => String) = throw new TypeError(s"\n$message")
  }

  private def err(message: String, constraints: List[≡]) =
    TypeError { s"$message:\n${constraints.head}" }

  private def err(msg: String, lhs: PrenexForm, rhs: PrenexForm) =
    TypeError {
      s"$msg in:\nfun : ${lhs.toType.unparse}" +
      s"\narg : ${rhs.toType.unparse}"
    }

  // TYPE ORDERING

  /** @param σ0 the more general type
    * @param τ0 the less general type
    *
    * A more general type has fewer terms under any given context.
    * Thus, σ ⊆ τ means that σ is more general than τ and every
    * term of type σ can be used as a term of type τ.
    */
  implicit class GreaterTypeGenerality(σ: Type) {
    def ⊆ (τ: Type): Boolean =
      (PrenexForm(σ) ⊆? PrenexForm(τ)).isInstanceOf[Success[_, _]]
  }

  trait TrialAndError[S, T]
  case class Success[S, T](result: S) extends TrialAndError[S, T]
  case class Failure[S, T](lesson: T) extends TrialAndError[S, T]

  implicit class GreaterPrenexGenerality(σ_p: PrenexForm) {
    def ⊆? (τ_p: PrenexForm): TrialAndError[Map[α, Type], String] =
      try {
        val PrenexForm(all_σ, ex_σ, σ0) = σ_p
        val PrenexForm(all_τ, ex_τ, τ0) = τ_p
        val all     = Set(all_σ ++ ex_τ: _*)
        val ex      = Set(ex_σ ++ all_τ: _*)
        val mgs0    = resolveConstraints(all, σ0 ≡ τ0)
        val mgs     = captureSkolems_⊆(mgs0, σ_p, τ_p)
        // If we end up instantiating captured Skolems globally instead of
        // locally, then we may not have to convert σ_inst & τ_inst to
        // prenex form.
        //
        // The instantiation of τ is not an instantiation, but rather
        // the recall of what it has forgotten from the instantiation of
        // σ.
        val σ_inst = PrenexForm(requantify(all, ex, σ0 subst_α mgs)).toType
        val τ_inst = PrenexForm(requantify(all, ex, τ0 subst_α mgs)).toType
        if (! (σ_inst α_equiv τ_inst)) sys error {
          // this is a system error, not a type error
          s"""|Hey, not α-equivalent after unification:
              |${σ_inst.unparse}
              |${τ_inst.unparse}
              |""".stripMargin
        }
        Success(mgs)
      }
      catch { case e: TypeError =>
        Failure(s"${e.message}\n${e.getStackTrace take 20 mkString "\n"}")
      }
  }

  // THE ELIMINATION RULE (→∀∃E)
  def getResultTypeOfApplication(funType: Type, argType: Type): Type = {
    val (funPrenex, argPrenex) = (PrenexForm(funType), PrenexForm(argType))
    val PrenexForm(all_f, ex_f, σ1 → τ) = funPrenex
    val PrenexForm(all_x, ex_x, σ2    ) = argPrenex
    val mgs =
      PrenexForm(all_x, ex_x, σ2) ⊆? PrenexForm(ex_f, all_f, σ1) match {
        case Success(mgs) => mgs
        case Failure(msg) => TypeError { msg }
      }
    requantify(Set(all_f ++ all_x: _*), Set(ex_f ++ ex_x: _*), τ subst_α mgs)
  }

  // UNIFICATION UNDER A MIXED PREFIX

  case class ≡(lhs: Type, rhs: Type) {
    override def toString = s"${lhs.unparse}  ≡  ${rhs.unparse}"
  }
  implicit class makeEqualityConstraint(lhs: Type) {
    def ≡(rhs: Type) = new ≡(lhs, rhs)
  }

  private type DegreeOfFreedom = Set[α]

  def resolveConstraints(dog: List[α], constraints: ≡ *): Map[α, Type] =
    resolveConstraints(Set(dog: _*), constraints: _*)

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

      case α(a1) ≡ α(a2) :: rest if a1 == a2 =>
        loop(rest)

      case (a: α) ≡ τ :: rest =>
        if (dog contains a) {
          val mgs = loop(rest map {
            case lhs ≡ rhs => (lhs subst (a, τ)) ≡ (rhs subst (a, τ))
          })
          mgs updated (a.binder, τ subst mgs)
        }
        else τ match {
          case b: α if dog contains b =>
            loop(b ≡ a :: rest)
          case _ =>
            err("trying to unify rigid type variable", constraints)
        }

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

  // THE INCARCERATION OF SKOLEMS

  def captureSkolems(mgs: Map[α, Type], lhs: PrenexForm, rhs: PrenexForm):
      Map[α, Type] = {
    import UnificationHelpers._
    val all = Set.empty[α] ++ lhs.all ++ rhs.all
    val ex  = Set.empty[α] ++ lhs.ex  ++ rhs.ex
    val either = all ++ ex
    val mgsAfterCapturing: Map[α, Type] = mgs map { case (a, τ) =>
      τ match {
        // universal unified to universal, do nothing, or:
        // universal unified to existential, do nothing beyond
        // the deletion of the universal, which is already done
        case b: α if either contains b =>
          (a, b)

        // unified to something not bound here, freak out
        case b: α =>
          err(s"$a unified to out-of-scope name $b", lhs, rhs)

        // universal unified to a nontrivial type, tons of work
        case τ0 =>
          val τ = (ex & unbound(τ0)).foldRight(τ0) {
            case (e, τ) =>
              // any existential in a nontrivial type unified to
              // a universal cannot appear anywhere outside.
              // make sure of that.
              if (count(e, τ0) != count(e, lhs.τ, rhs.τ))
                err(s"the existential $e in ${τ0.unparse} escaped!", lhs, rhs)
              // compute depth (number of greatest nesting to the
              // left of function arrows)
              val depthInside  = depth(e, τ0)
              val depthOutside = depth(e, lhs.τ, rhs.τ)
              assert(depthInside >= 0 && depthOutside >= 0)
              // if depth parities are equal inside & out,
              // quantify e existentially; otherwise universally
              //
              // Instead of laboriously requantify on instantiation,
              // we may choose to quantify the existential from
              // outside once it's certain that it did not escape.
              // For now, we use the slow method so that we don't
              // have to think about possible loopholes in the fast
              // method.
              if (depthInside % 2 == depthOutside % 2)
                ∃(e.binder.name) { x => τ subst (e, x) }
              else
                ∀(e.binder.name) { x => τ subst (e, x) }
          }
          (a, τ)
      }
    }
    mgsAfterCapturing
  }

  // capture skolems in the process of proving lhs ⊆ rhs
  def captureSkolems_⊆(mgs: Map[α, Type], lhs: PrenexForm, rhs: PrenexForm):
      Map[α, Type] = {
    import UnificationHelpers._
    val all = Set.empty[α] ++ lhs.all ++ rhs.ex
    val ex  = Set.empty[α] ++ lhs.ex  ++ rhs.all
    val either = all ++ ex
    val mgsAfterCapturing: Map[α, Type] = mgs map { case (a, τ) =>
      τ match {
        // universal unified to universal, do nothing, or:
        // universal unified to existential, do nothing beyond
        // the deletion of the universal, which is already done
        case b: α if either contains b =>
          (a, b)

        // unified to something not bound here, freak out
        case b: α =>
          err(s"$a unified to out-of-scope name $b", lhs, rhs)

        // universal unified to a nontrivial type, tons of work
        case τ0 =>
          val τ = (ex & unbound(τ0)).foldRight(τ0) {
            case (e, τ) =>
              // any existential in a nontrivial type unified to
              // a universal cannot appear anywhere outside.
              // make sure of that.
              if (count(e, τ0) != count(e, lhs.τ, rhs.τ))
                err(s"the existential $e in ${τ0.unparse} escaped!", lhs, rhs)
              // compute depth (number of greatest nesting to the
              // left of function arrows)
              val depthInside  = depth(e, τ0)
              val depthOutside = depth(e, lhs.τ, rhs.τ)
              assert(depthInside >= 0 && depthOutside >= 0)
              // if depth parities are equal inside & out,
              // quantify e universally; otherwise existentially
              //
              // Instead of laboriously requantify on instantiation,
              // we may choose to quantify the existential from
              // outside once it's certain that it did not escape.
              // For now, we use the slow method so that we don't
              // have to think about possible loopholes in the fast
              // method.
              if (depthInside % 2 == depthOutside % 2)
                ∀(e.binder.name) { x => τ subst (e, x) }
              else
                ∃(e.binder.name) { x => τ subst (e, x) }
          }
          (a, τ)
      }
    }
    mgsAfterCapturing
  }

  // STABLE LINEARIZATION OF QUANTIFIERS

  def requantify(_all: Set[α], _ex: Set[α], τ: Type): Type = {
    import UnificationHelpers._
    val yetUnbound = unbound(τ)
    val all = _all.filter(yetUnbound contains _).toList.
              sortBy(a => ordinal(a, τ))
    val ex  = _ex .filter(yetUnbound contains _).toList.
              sortBy(a => ordinal(a, τ))
    all.foldRight[Type](
      ex.foldRight[Type](τ) {
        case (a, τ) => ∃(a.binder.name) { x => τ subst (a, x) }
      }
    ) {
      case (a, τ) => ∀(a.binder.name) { x => τ subst (a, x) }
    }
  }

  // HELPERS

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
