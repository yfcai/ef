trait Unification extends Syntax with PrenexForm {
  unification =>

  // ERROR HANDLING

  class TypeError(message: String) extends Exception(message)
  object TypeError {
    def apply(message: => String) = throw new TypeError(s"\n$message")
  }

  private def err(message: String, constraints: List[≡]) =
    TypeError { s"$message:\n${constraints.head}" }

  private def err(msg: String) = TypeError {
    "$msg in:\nfun : ${lhs.toType.unparse}" +
      "\narg : ${rhs.toType.unparse}"
  }

  // TYPE ORDERING

  /** @param σ0 the more general type
    * @param τ0 the less general type
    *
    * A more general type has fewer terms under any given context.
    * Thus, σ ⊆ τ means that σ is more general than τ and every
    * term of type σ can be used as a term of type τ.
    */
  implicit class GreaterTypeGenerality(σ0: Type) {
    def ⊆ (τ0: Type): Boolean = try {
      val PrenexForm(all_σ, ex_σ, σ) = PrenexForm(σ0)
      val PrenexForm(all_τ, ex_τ, τ) = PrenexForm(τ0)
      val mgs   = resolveConstraints(all_σ ++ ex_σ, σ ≡ τ)
      val mgs_∀ = mgs filter {
        case (k, v: α) => (all_σ contains k) &&
                          ((all_τ contains v) || (ex_τ contains v))
        case _         => false
      }
      val mgs_∃ = mgs filter {
        case (k, v: α) => (ex_σ contains k) && (ex_τ contains v)
        case _         => false
      }
      val mgs_→ = mgs filter {
        case (k, v) => (all_σ contains k) && ! v.isInstanceOf[α]
      }
      // all legal unifications are captured in mgs_∀, _∃, or _→.
      // if anything else is present, then it is illegal.
      if (mgs_∀.size + mgs_∃.size + mgs_→.size != mgs.size) {
        // println(s"reason for rejection = illegal unification")
        return false
      }
      // if mgs_∀ and mgs_∃ are not bijections, then we have illegal
      // unifications as well.
      {
        val image_∀ = Set.empty ++ mgs_∀.map(_._2)
        val image_∃ = Set.empty ++ mgs_∃.map(_._2)
        if (image_∀.size != mgs_∀.size ||
            image_∃.size != mgs_∃.size) {
          // println(
          //   s"reason for rejection = variable unification not bijective"
          // )
          return false
        }
      }
      // Skolems must not escape!
      captureSkolems(mgs_→, all_τ ++ ex_τ, σ, τ) // raises TypeError
      true
    } catch {
      case e: TypeError =>
        false
    }
  }

  // THE ELIMINATION RULE (→∀∃E)

  def getResultTypeOfApplication(funType: Type, argType: Type): Type = {
    val (funPrenex, argPrenex) = (PrenexForm(funType), PrenexForm(argType))
    val PrenexForm(all_f, ex_f, σ1 → τ) = funPrenex
    val PrenexForm(all_x, ex_x, σ2    ) = argPrenex
    val all     = Set(all_f ++ all_x: _*)
    val ex      = Set( ex_f ++  ex_x: _*)
    val mgs0    = resolveConstraints(all, σ1 ≡ σ2)
    val mgs     = captureSkolems(mgs0, funPrenex, argPrenex)
    // If we end up instantiating captured Skolems globally instead of
    // locally, then we may not have to convert σ1_inst & σ2_inst to
    // prenex form.
    val σ1_inst = PrenexForm(requantify(all, ex, σ1 subst_α mgs)).toType
    val σ2_inst = PrenexForm(requantify(all, ex, σ2 subst_α mgs)).toType
    if (! (σ1_inst α_equiv σ2_inst)) TypeError {
      s"""|Hey, not α-equivalent after unification:
          |${σ1_inst.unparse}
          |${σ2_inst.unparse}
          |""".stripMargin
    }
    requantify(all, ex, τ subst_α mgs)
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

  // THE INCARCERATION OF SKOLEMS

  // skolem capturing for application
  def captureSkolems(mgs: Map[α, Type], lhs: PrenexForm, rhs: PrenexForm):
      Map[α, Type] = {
    val all = Set.empty[α] ++ lhs.all ++ rhs.all
    val ex  = Set.empty[α] ++ lhs.ex  ++ rhs.ex
    captureSkolems(mgs, all, ex, lhs.τ, rhs.τ)
  }

  // skolem capturing for deciding the generality partial order on types
  def captureSkolems(mgs: Map[α, Type], skolems: List[α],
                     lhs_τ: Type, rhs_τ: Type): Map[α, Type] =
    captureSkolems(mgs, Set.empty, Set(skolems: _*), lhs_τ, rhs_τ)

  // all-purpose skolem capturing (may want to split)
  def captureSkolems(
    mgs  : Map[α, Type],
    all  : Set[α],
    ex   : Set[α],
    lhs_τ: Type,
    rhs_τ: Type
  ): Map[α, Type] =
  {
    import UnificationHelpers._
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
          err(s"$a unified to out-of-scope name $b")

        // universal unified to a nontrivial type, tons of work
        case τ0 =>
          val τ = (ex & unbound(τ0)).foldRight(τ0) {
            case (e, τ) =>
              // any existential in a nontrivial type unified to
              // a universal cannot appear anywhere outside.
              // make sure of that.
              if (count(e, τ0) != count(e, lhs_τ, rhs_τ))
                err(s"the existential $e in ${τ0.unparse} escaped!")
              // compute depth (number of greatest nesting to the
              // left of function arrows)
              val depthInside  = depth(e, τ0)
              val depthOutside = depth(e, lhs_τ, rhs_τ)
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
