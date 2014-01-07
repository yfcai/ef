/** Algorithms reported in:
  * Didier Le Botlan and Didier Rémy.
  * ML^F: Raising ML to the power of System F.
  */
trait MLF extends Syntax {

  case class UnificationError(msg: String) extends Exception(msg)
  private def error(msg: String) = throw UnificationError(msg)

  case object ⊥ extends LeafTag {
    def genus = Type
    def man = manifest[this.type]
    def apply() = ∙(this, this)

    def unapply(t: Tree): Boolean = is(t)

    def is(t: Tree): Boolean = t match {
      case ∙(⊥, ⊥) => true
      case _ => false
    }

    override def unparse(t: Tree): String = "⊥"
  }

  object BinderSpecSugar {
    implicit class StringToBound(α: String) {
      def ≡(s: String): (String, BinderSpec) = ≡(Type.parse(s).get)
      def ⊒(s: String): (String, BinderSpec) = ⊒(Type.parse(s).get)
      def ≡(τ: Tree): (String, BinderSpec) =
        (α, BinderSpec(RigidUniversal, α, τ))
      def ⊒(τ: Tree): (String, BinderSpec) =
        (α, BinderSpec(BoundedUniversal, α, τ))
    }
  }

  def isPolyType(τ: Tree): Boolean =
    τ.tag.isInstanceOf[Binder] || ⊥.is(τ)

  def isMonoType(τ: Tree): Boolean = ! isPolyType(τ)

  /** @param prefix
    *        MLF Prefix. All universals must have a rigid or
    *        flexible bound. There must be no existentials.
    */
  def unify(prefix: BinderPrefix, τ1: Tree, τ2: Tree):
      Status[BinderPrefix] = {

    // helpers

    type Domain = Status[BinderPrefix]

    def err(msg: String): Nothing =
      error(errmsg(msg))

    def failure(msg: String): Status[BinderPrefix] =
      Failure(errmsg(msg))

    def errmsg(msg: String): String = s"""|$msg
        |τ1 = ${τ1.unparse}
        |τ2 = ${τ2.unparse}
        |under the prefix
        |${pretty(prefix)}
        |""".stripMargin

    def isPoly(α: String): Boolean =
      prefix.contains(α) && isPolyType(prefix(α).annotation)
    def isMono(α: String): Boolean =
      prefix.contains(α) && isMonoType(prefix(α).annotation)

    def notInDom(τ: Tree): Boolean = τ match {
      case æ(β) => ! prefix.contains(β)
      case _ => true
    }

    import BinderSpecSugar._

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
              case (Success(prefix), (σ1, σ2)) => unify(prefix, σ1, σ2)
            }
        // case 3: incongruent type constructors
        else
          return failure("incongruent type constructors")

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
            return failure(
              "case 5.1: if (α ≡ ⊥) ∈ Q, then fail.")
          case _ =>
            ()
        }
        val σ = spec.annotation

        // case 5.2: if σ is ⊥ then return Q ⇐ (α = τ).
        if (⊥ is σ)
          // deviation point from MLF: prefix is a map, not a list,
          // hence no reordering and no verification.
          // we shall linearize the prefix once & for all when it's done.
          return Success(prefix + (α ≡ τ))

        // line 5.3: let ∀(Q')τ' be σ with dom(Q), dom(Q') disjoint.

        val unbound = detachAll(σ, prefix.keySet)
        val Q1 = mkPrefix(unbound._1)
        val τ1 = unbound._2

        // case 5.4: if ♢ is =, check that Q' is rigid, otherwise fail.
        if (
          spec.tag == RigidUniversal &&
            Q1.find(_._2.tag == RigidUniversal) != None
        )
          return failure("case 5.4: if ♢ is =, " +
            "check that Q' is rigid, otherwise fail.")

        // line 5.5: let Q" be (QQ') ⇐ (α = τ')
        // case 5.6: return unify(Q", α, τ)
        val Q2 = (prefix ++ Q1) + (α ≡ τ1)
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

        // line 6.1: let ♢ be either ⊒, if both ♢₁ and ♢₂ are ⊒,
        //           and = otherwise.
        val (spec1, spec2) = (prefix(α1), prefix(α2))
        val (σ1, σ2) = (spec1.annotation, spec2.annotation)
        val ♢ = (spec1.tag, spec2.tag) match {
          case (BoundedUniversal, BoundedUniversal) =>
            BoundedUniversal
          case _ =>
            RigidUniversal
        }

        // case 6.2: if σ₁ and σ₂ are ⊥ then
        //           return Q ⇐ (α₁ ♢ ⊥) ⇐ (α₂ = α₁)
        if (⊥.is(σ1) && ⊥.is(σ2))
          return Success(
            prefix.updated(α1, BinderSpec(♢, α1, ⊥())) +
              (α2 ≡ æ(α1)))

        // case 6.3: if σi is ⊥ and ♢i is = then fail
        if (⊥.is(σ1) && spec1.tag == RigidUniversal)
          return failure(s"$α1 = ⊥")
        if (⊥.is(σ2) && spec2.tag == RigidUniversal)
          return failure(s"$α2 = ⊥")

        // case 6.4: if σ₁ is ⊥ then return Q ⇐ (α₁ = α₂)
        // case 6.5: if σ₂ is ⊥ then return Q ⇐ (α₂ = α₁)
        if (⊥ is σ1) return Success(prefix + (α1 ≡ æ(α2)))
        if (⊥ is σ2) return Success(prefix + (α2 ≡ æ(α1)))

        // line 6.6: let ∀(Q₁)τ₁ be σ₁ and ∀(Q₂)τ₂ be τ₂
        //           with dom(Q), dom(Q₁), dom(Q₂) disjoint.
        val unbound1 = detachAll(σ1, prefix.keySet)
        val Q1       = mkPrefix(unbound1._1)
        val τ1       = unbound1._2
        val unbound2 = detachAll(σ2, prefix.keySet ++ Q1.map(_._2.x))
        val Q2       = mkPrefix(unbound2._1)
        val τ2       = unbound2._2

        // line 6.7: let Q₀ be unify(QQ₁Q₂, τ₁, τ₂)
        val Q0 = unify(prefix ++ Q1 ++ Q2, τ1, τ2) match {
          case Success(q) => q
          case Failure(s) => return Failure(s)
        }

        // line 6.8: let (Q₃, Q') be Q₀ ↑ dom(Q)
        val q3qp = upArrow(Q0, prefix.keySet)
        val Q3 = q3qp._1
        val QP = linearizePrefix(q3qp._2)

        // case 6.9: if ♢₁ is = and (Q₃) ¬ (σ₁ E ∀(Q')τ₁) then fail
        // case 6.A: if ♢₂ is = and (Q₃) ¬ (σ₂ E ∀(Q')τ₂) then fail

        // verification of sharing is too conservative.
        // "choose id auto" triggers it, if fully written out.

        def rigidityViolation(prefix: Seq[BinderSpec], τ1: Tree, τ2: Tree):
            Option[String] = {
          val (ρ1, ρ2) = (reattach(prefix, τ1), reattach(prefix, τ2))
          if (equiv(ρ1, ρ2))
            None
          else
            Some(
              s"case 6.9/A: not equivalent:\n" +
                s"       σ = ${τ1.unparse}\nand\n" +
                s"  ∀(Q')τ = ${τ2.unparse}\nnormalized to\n" +
                s"       σ ~ ${normalize(ρ1).unparse}\n" +
                s"  ∀(Q')τ ~ ${normalize(ρ2).unparse}\n" +
                s"where Q' =\n${pretty(prefix)}")
        }

        val Q3L = linearizePrefix(Q3)
        rigidityViolation(Q3L, σ1, reattach(QP, τ1)).map(
          s => return failure(s))
        rigidityViolation(Q3L, σ2, reattach(QP, τ2)).map(
          s => return failure(s))

        // line 6.B: let σ₃ be ∀(Q')τ₁
        val σ3 = τ1 boundBy QP

        // case 6.C: return (Q3) ⇐ (α₁ ♢ σ₃) ⇐ (α₂ = α₁)
        Success(Q3.updated
          (α1, BinderSpec(♢, α1, σ3)) +
          (α2 ≡ æ(α1)))

      case _ =>
        err("missed case")
    }
  }

  def mkPrefix(list: Seq[BinderSpec]): Seq[(String, BinderSpec)] =
    list.map {
      case BinderSpec(UniversalQuantification, α, Seq()) =>
        (α, BinderSpec(BoundedUniversal, α, ⊥()))

      case flexible @ BinderSpec(BoundedUniversal, α, _) =>
        (α, flexible)

      case rigid @ BinderSpec(RigidUniversal, α, _) =>
        (α, rigid)

      case otherwise =>
        error(s"unexpected binder $otherwise in prefix\n$list")
    }

  def detachAll(σ: Tree, toAvoid: Set[String]) =
    σ.unbindAll(toAvoid,
      UniversalQuantification, BoundedUniversal, RigidUniversal)

  def detachPrefix(τ: Tree, toAvoid: Set[String]):
      (Seq[(String, BinderSpec)], Tree) = {
    val unbound = detachAll(τ, toAvoid)
    (mkPrefix(unbound._1), unbound._2)
  }

  // quantify parsimoniously, leave rigid quantifiers in place
  def reattach(prefix: Seq[BinderSpec], body: Tree): Tree =
    prefix.foldRight(body)(reattachment)

  def reattach(prefix: BinderPrefix, body: Tree): Tree =
    reattach(linearizePrefix(prefix), body)

  def reattachFlexible(prefix: Seq[BinderSpec], body: Tree): Tree =
    prefix.foldRight(body)(reattachFlexibility)

  def reattachUniversal(prefix: Seq[BinderSpec], body: Tree): Tree =
    prefix.foldRight(body)(reattachUniversality)

  val reattachment: (BinderSpec, Tree) => Tree = {
    case (spec, body) if ! body.freeNames.contains(spec.x) =>
      body
    case (spec, body) =>
      spec.tag.bind(spec.x, spec.annotations :+ body: _*)
  }

  val reattachFlexibility: (BinderSpec, Tree) => Tree = {
    case (BinderSpec(RigidUniversal, α, Seq(τ)), body) =>
      body.subst(æ(α), τ)
    case (spec, body) =>
      reattachment(spec, body)
  }

  val reattachUniversality: (BinderSpec, Tree) => Tree = {
    case (BinderSpec(BoundedUniversal, α, Seq(⊥())), body)
        if body.freeNames.contains(α) =>
      UniversalQuantification.bind(α, body)
    case (BinderSpec(BoundedUniversal, α, Seq(τ)), body) =>
      body.subst(æ(α), τ)
    case (spec, body) =>
      reattachFlexibility(spec, body)
  }

  // assume τ has monotype body, else it won't work.
  def normalize(τ: Tree): Tree = {
      val (prefix, body) = detachPrefix(τ, Set.empty)
      normalize(prefix.map(x => x)(collection.breakOut):
          BinderPrefix, body)
    }

  def normalize(prefix: Seq[BinderSpec], body: Tree): Tree =
    normalize(prefix.map(spec => (spec.x, spec))(collection.breakOut):
        BinderPrefix, body)

  def normalize(prefix: BinderPrefix, body: Tree): Tree =
    reattachUniversal(
      linearizePrefix(prefix).map({
        case BinderSpec(tag, α, annotations) =>
          BinderSpec(tag, α, annotations.map(normalize))
      }), body)

  def equiv(τ1: Tree, τ2: Tree): Boolean =
    normalize(τ1) α_equiv normalize(τ2)

  // make sure a type has only monotypes in its body
  // make sure that all bounds have only monotypes in their bodies
  def ensureMonotypeBody(τ: Tree): Tree = {
    import BinderSpecSugar._
    def loop(τ: Tree, toAvoid: Set[String]):
        (List[BinderSpec], Tree, Set[String]) = τ match {
      case ⊹(binder: Binder, _*) =>
        val (∙(_, β), children) = binder.unbind(τ, toAvoid).get
        val annotations = children.init.map(ensureMonotypeBody)
        val (specs, body, newThingsToAvoid) =
          loop(children.last, toAvoid + β)
        val spec = BinderSpec(binder, β, annotations)
        (spec :: specs, body, newThingsToAvoid)

      // function arrow, functor application et co.
      case ⊹(tag, children @ _*) =>
        val (newSpecs, newChildren, newThingsToAvoid) =
          children.foldRight[(List[BinderSpec], List[Tree], Set[String])](
            (Nil, Nil, τ.freeNames)
          )({
            case (child0 @ ⊹(binder: Binder, bodies @ _*),
                  (specs0, children, toAvoid0)) =>
              val β = Subscript.
                newName(binder.defaultNameOf(child0), toAvoid0)
              val (specs, child, toAvoid) = loop(child0, toAvoid0 + β)
              val spec = BinderSpec(RigidUniversal, β, child)
              (specs ++ (spec :: specs0), æ(β) :: children, toAvoid)

            case (child0, (specs0, others, toAvoid0)) =>
              val (specs, child, toAvoid) = loop(child0, toAvoid0)
              (specs ++ specs0, child :: others, toAvoid)
          })
        (newSpecs, ⊹(tag, newChildren: _*), newThingsToAvoid)

      case _ =>
        (Nil, τ, toAvoid)
    }

    val (specs, monobody, _) = loop(τ, τ.freeNames)
    monobody.boundBy(specs)
  }

  def upArrow(prefix: BinderPrefix, sink: Set[String]):
      (BinderPrefix, BinderPrefix) = {
    var frontier = sink
    var acc: BinderPrefix = Map.empty
    while (! frontier.isEmpty) {
      val news = frontier.flatMap(x => prefix.get(x).map(y => (x, y)))
      acc = acc ++ news
      frontier = news.flatMap(_._2.annotation.freeNames) -- acc.keySet
    }
    (acc, prefix -- acc.keySet)
  }
}
