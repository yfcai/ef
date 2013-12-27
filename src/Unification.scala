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

  trait TrialAndError[S, T]
  case class Success[S, T](get: S)     extends TrialAndError[S, T]
  case class Failure[S, T](message: T) extends TrialAndError[S, T]

  /** @param σ0 the more general type
    * @param τ0 the less general type
    *
    * A more general type has fewer terms under any given context.
    * Thus, σ ⊑ τ means that σ is more general than τ and every
    * term of type σ can be used as a term of type τ.
    */
  implicit class GreaterTypeGenerality(σ: Type) {
    def ⊑ (τ: Type): Boolean =
      (PrenexForm(σ) ⊑? PrenexForm(τ)).isInstanceOf[Success[_, _]]
  }

  implicit class GreaterPrenexGenerality(lhsPrenex: PrenexForm) {
    def ⊑?(rhsPrenex: PrenexForm):
        TrialAndError[Map[α, Type], String] =
      try {
        val PrenexForm(all0, ex0, σ0) = lhsPrenex
        val PrenexForm(all1, ex1, σ1) = rhsPrenex
        val all     = Set(all0 ++ ex1: _*)
        val ex      = Set(ex0 ++ all1: _*)
        val mgs0    = resolveConstraints(all, σ0 ≡ σ1)
        val mgs     = captureSkolems(mgs0, lhsPrenex, rhsPrenex)
        Success(mgs)
      }
      catch {
        case e: TypeError =>
          Failure(s"${e.message}\nin\n${
            e.getStackTrace.take(20) mkString "\n"
          }")
      }
  }

  // THE ELIMINATION RULE (→∀∃E)
  def getResultTypeOfApplication(funType: Type, argType: Type): Type = {
    val argPrenex = PrenexForm(argType)
    val funPrenex = PrenexForm(funType)
    val PrenexForm(all_x, ex_x, σ0    ) = argPrenex
    val PrenexForm(all_f, ex_f, σ1 → τ) = funPrenex match {
      case PrenexForm(all, _, a: α) if all contains a =>
        return ∀(a.binder.name){ x => x } // operator is absurd
      case _ =>
        funPrenex
    }
    val mgs = (argPrenex ⊑? PrenexForm(ex_f, all_f, σ1)) match {
      case Success(mgs) => mgs
      case Failure(msg) => TypeError { msg }
    }
    val σ0_inst = PrenexForm(
      requantify(all_f ++ all_x, ex_f ++ ex_x, σ0 subst_α mgs)).toType
    val σ1_inst = PrenexForm(
      requantify(all_f ++ all_x, ex_f ++ ex_x, σ1 subst_α mgs)).toType
    if (! (σ0_inst α_equiv σ1_inst)) TypeError {
      s"""|Hey, not α-equivalent after unification:
          |
          |  ${σ0_inst.unparse}
          |  ${σ1_inst.unparse}
          |
          |in the application where
          |
          |  fun : ${funType.unparse}
          |  arg : ${argType.unparse}
          |""".stripMargin
    }
    if (false) { // debug information
      println(s"  actual param : ${σ0_inst.unparse}")
      println(s"  formal param : ${σ1_inst.unparse}")
    }
    requantify(all_f ++ all_x, ex_x, requantify(Nil, ex_f, τ) subst_α mgs)
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
    val all = Set.empty[α] ++ lhs.all ++ rhs.ex
    val ex  = Set.empty[α] ++ lhs.ex ++ rhs.all
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
              // quantify e universally; otherwise existentially.
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

  // STABLE LINEARIZATION OF QUANTIFIERS

  def requantify(all: Seq[α], ex: Seq[α], τ: Type): Type =
    requantify(Set(all: _*), Set(ex: _*), τ)

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
        case ₌:(lhs, rhs)       => sys error "pending ADT functor variance"
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
