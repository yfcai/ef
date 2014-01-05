/** Algorithms reported in:
  * Didier Le Botlan and Didier Rémy.
  * ML^F: Raising ML to the power of System F.
  */
trait MLF extends Syntax {
  case object ⊥ extends LeafTag {
    def genus = Type
    def man = manifest[this.type]
    def apply() = ∙(this, this)
    def unapply(t: Tree): Boolean = t match {
      case ∙(⊥, ⊥) => true
      case _ => false
    }
  }

  type BinderPrefix = Map[String, BinderSpec]

  trait Status[+T]
  case class Success[+T](get: T) extends Status[T]
  case class Failure[+T](message: String) extends Status[T]

  /** @param prefix
    *        MLF Prefix. All universals must have a rigid or
    *        flexible bound. There must be no existentials.
    */
  def unify(prefix: BinderPrefix, τ1: Tree, τ2: Tree):
      Status[BinderPrefix] = {

    // helpers

    type Domain = Status[BinderPrefix]

    def err(msg: String): Nothing =
      sys error errmsg(msg)

    def fail(msg: String): Status[BinderPrefix] =
      Failure(errmsg(msg))

    def errmsg(msg: String): String = s"""|$msg
        |τ1 = ${τ1.unparse}
        |τ2 = ${τ2.unparse}
        |under the prefix
        |${prefix mkString "\n"}
        |""".stripMargin

    def isPolyType(τ: Tree): Boolean = τ.tag.isInstanceOf[Binder]
    def isMonoType(τ: Tree): Boolean = ! isPolyType(τ)

    def isPoly(α: String): Boolean =
      prefix.contains(α) && isPolyType(prefix(α).annotation)
    def isMono(α: String): Boolean =
      prefix.contains(α) && isMonoType(prefix(α).annotation)


    def makeMLFPrefix(list: Seq[BinderSpec]):
        Seq[(String, BinderSpec)] =
      list.map {
        case BinderSpec(UniversalQuantification, α, Seq()) =>
          (α, BinderSpec(BoundedUniversal, α, ⊥()))

        case flexible @ BinderSpec(BoundedUniversal, α, _) =>
          (α, flexible)

        case rigid @ BinderSpec(RigidUniversal, α, _) =>
          (α, rigid)

        case otherwise =>
          err("unexpected binder in MLF prefix: $otherwise")
      }

    def notInDom(τ: Tree): Boolean = τ match {
      case æ(β) => ! prefix.contains(β)
      case _ => true
    }

    // unification starts

    (τ1, τ2) match {
      // guard: τ1 & τ2 are monotypes
      case _ if isPolyType(τ1) || isPolyType(τ2) =>
        err("polytype encounted")

      // case 1: unification is done
      case (æ(α), æ(β)) if α == β =>
        Success(prefix)

      // case 2, 3: type constructors
      case (⊹(tag1, children1 @ _*), ⊹(tag2, children2 @ _*)) =>
        // case 2: identical type constructors
        if (tag1 == tag2)
          (children1, children2).zipped.
            foldLeft[Domain](Success(prefix)) {
              case (fail: Failure[_], _) => fail
              case (Success(prefix), (τ1, τ2)) => unify(prefix, τ1, τ2)
            }
        // case 3: incongruent type constructors
        else
          fail("incongruent type constructors")

      // case 4: monotype in prefix
      case (æ(α), τ) if isMono(α) =>
        unify(prefix, τ, prefix(α).annotation)
      case (τ, æ(α)) if isMono(α) =>
        unify(prefix, τ, prefix(α).annotation)

      // case 5: polytype in prefix
      case (æ(α), τ)
          // condition 5a: τ ∉ dom(Q)
          if notInDom(τ) &&
          // condition 5b: σ ∉ Τ (i. e., σ is not a monotype)
          isPoly(α) =>
        // case 5.1: if (α ≡ ⊥) ∈ Q, then fail.
        val spec = prefix(α)
        spec match {
          case BinderSpec(RigidUniversal, _, Seq(⊥())) =>
            return fail(
              "case 5.1: if (α ≡ ⊥) ∈ Q, then fail.")
          case _ =>
            ()
        }
        val σ = spec.annotation

        // case 5.2: if σ is ⊥ then return Q ⇐ (α = τ).
        if (⊥ unapply σ)
          // deviation point from MLF: prefix is a map, not a list,
          // hence no reordering and no verification.
          // we shall linearize the prefix once & for all when it's done.
          return Success(
            prefix.updated(α, BinderSpec(RigidUniversal, α, τ)))

        // line 5.3: let ∀(Q')τ' be σ with dom(Q), dom(Q') disjoint.

        val unbound = σ.unbindAll(prefix.keySet,
          UniversalQuantification, BoundedUniversal, RigidUniversal)
        val Q1 = makeMLFPrefix(unbound._1)
        val τ1 = unbound._2

        // case 5.4: if ♢ is =, check that Q' is rigid, otherwise fail.
        if (
          spec.tag == RigidUniversal &&
            Q1.find(_._2.tag == RigidUniversal) != None
        )
          return fail("case 5.4: if ♢ is =, " +
            "check that Q' is rigid, otherwise fail.")

        // line 5.5: let Q" be (QQ') ⇐ (α = τ')
        // case 5.6: return unify(Q", α, τ)
        val Q2 = (prefix ++ Q1).updated(α,
          BinderSpec(RigidUniversal, α, τ1))
        unify(Q2, æ(α), τ)

      // case 5 (converse): polytype in prefix
      case (τ, æ(α))
          // condition 5a: τ ∉ dom(Q)
          if notInDom(τ) &&
          // condition 5b: σ ∉ Τ (i. e., σ is not a monotype)
          isPoly(α) =>
        unify(prefix, æ(α), τ)

      // case 6: (α1, α2) when α1 ≠ α2
      // and their annotations are polytypes
      case (æ(α1), æ(α2))
          if α1 != α2 && isPoly(α1) && isPoly(α2) =>
        ???

      case _ =>
        err("missed case")
    }
  }
}
