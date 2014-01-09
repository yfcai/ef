/** Prenex forms for Existential F */
trait Prenex extends Syntax {
  case class Prenex(prefix: Seq[PrenexSpec], body: Tree) {
    def toType: Tree = Prenex.bind(prefix, body)

    def flipPrefix: Seq[PrenexSpec] = prefix.map({
      case PrenexSpec(tag, x, annotations @ _*) =>
        PrenexSpec(Prenex.flipTag(tag), x, annotations: _*)
    })

    def normalize: Tree =
      Prenex.normalize(prefix, body)

    def indexOf(α: String): Int =
      Prenex.indexOf(α, body)

    def depth(α: String): Int =
      Prenex.depth(α, body)

    def count(α: String): Int =
      Prenex.count(α, body)

    lazy val freeNames: Set[String] =
      body.freeNames -- prefix.map(_.x)
  }

  object Prenex {
    def normalize(prefix: Seq[PrenexSpec], body: Tree): Tree = {
      val topo = topologicalOrder(prefix)
      val specs =
        prefix.withFilter(body.freeNames contains _.x).map(
          spec => (spec, (topo(spec.x), indexOf(spec.x, body)))
        ).sortBy(_._2).map(_._1)
      bind(specs, body)
    }

    def bind(prefix: Seq[PrenexSpec], body: Tree): Tree =
      body.boundBy(prefix.map(_.toBinderSpec))

    // consider merging with topological order of binderspecs
    def topologicalOrder(prefix: Seq[PrenexSpec]):
        Map[String, Int] =
      topologicalOrder(
        prefix.map(s => (s.x, s))(collection.breakOut):
            Map[String, PrenexSpec])

    def topologicalOrder(prefix: Map[String, PrenexSpec]):
        Map[String, Int] = {
      // copied from Syntax.topologicalOrder
      val graph = prefix map {
        case (α, spec) =>
          (α,
            spec.annotations.flatMap(_.freeNames)(collection.breakOut):
                Set[String])
      }
      var distance = -1
      var toVisit  = graph.keySet
      var result   = Map.empty[String, Int]
      while (! toVisit.isEmpty) {
        val frontier = toVisit.filter {
          α => graph(α).find(toVisit contains _) == None
        }
        if (frontier.isEmpty)
          sys error s"cycle detected in prenex topology"
        distance = distance +  1
        toVisit  = toVisit  -- frontier
        result   = result   ++ frontier.map(α => (α, distance))
      }
      result
    }

    def indexOf(α: String, body: Tree): Int =
      body.preorder.indexOf(æ(α))

    // is there a standard name?
    //
    // max number of function arrows to whom
    // a fixed occurrence of α is a left descendant
    // --OR--
    // max number of type constructors to whom
    // a fixed occurrence of α is a contravariant descendant
    //
    // number is -∞ if α does not occur here.
    def depth(α: String, τ: Tree): Int = τ match {
      case σ → τ =>
        Math.max(depth(α, σ) + 1, depth(α, τ))

      // only know how to recurse down to unannotated binders
      case τ @ ⊹(tag: Binder, _*)
          if tag == UniversalQuantification
          || tag == ExistentialQuantification =>
        depth(α, tag bodyOf τ)

      case ⊹(_, _*) =>
        sys error s"depth of ${τ.unparse}"
      case æ(β) if α == β =>
        0
      case _ =>
        Int.MinValue
    }

    // number of occurrences of α
    def count(α: String, τ: Tree): Int = τ match {
        case ⊹(_, children @ _*) =>
          children.map(σ => count(α, σ)).fold(0)(_ + _)
        case æ(β) if α == β =>
          1
        case _ =>
          0
      }

    def flipTag(tag: Binder): Binder = tag match {
      case UniversalQuantification =>
        ExistentialQuantification
      case ExistentialQuantification =>
        UniversalQuantification
      case UniversalBound =>
        ExistentialBound
      case ExistentialBound =>
        UniversalBound
      case UniversalUncertainty =>
        ExistentialUncertainty
      case ExistentialUncertainty =>
        UniversalUncertainty
    }

    def apply(τ: Tree): Prenex =
      Prenex(τ, Set.empty[String])._1

    def apply(τ: Tree, types: Tree*): Seq[Prenex] =
      Prenex(τ +: types, Set.empty[String])._1

    def apply(τ: Tree, toAvoid: Set[String]): (Prenex, Set[String]) = {
      val (rawPrefix, rawBody) = τ.unbindAll(toAvoid, _ => true)
      val undesirables1 = toAvoid ++ rawPrefix.map(_.x)
      val (prefix, undesirables2) = PrenexSpec(rawPrefix, undesirables1)
      val (pbody, undesirables3) = ofMonotype(rawBody, undesirables2)
      (Prenex(prefix ++ pbody.prefix, pbody.body), undesirables3)
    }

    def apply(types: Seq[Tree], toAvoid: Set[String]):
        (Seq[Prenex], Set[String]) =
      types.foldRight[(Seq[Prenex], Set[String])]((Nil, toAvoid)) {
        case (τ, (prenexes, toAvoid)) =>
          val (prenex, undesirables) = Prenex(τ, toAvoid)
          (prenex +: prenexes, undesirables)
      }

    def ofMonotype(monotype: Tree, toAvoid: Set[String]):
        (Prenex, Set[String]) = monotype match {
      case σ → τ =>
        val (Seq(ps, pt), undesirables) = Prenex(Seq(σ, τ), toAvoid)
        (Prenex(ps.flipPrefix ++ pt.prefix, →(ps.body, pt.body)),
          undesirables)

      case σ ₌ τ =>
        sys error s"""|
          |is functor covariant or contravariant or invariant?
          |we may want to distinguish those in the future
          |as different, additional tags. juxtaposition would
          |still be parsed as TypeApplication, but a module
          |should be able to refine each occurrence of it.
          |""".stripMargin

      case ⊹(tag, _) =>
        sys error s"object Prenex isn't aware of $tag"

      case leaf @ ∙(_, _) =>
        (Prenex(Nil, leaf), toAvoid)
    }
  }

  case class PrenexSpec(tag: Binder, x: String, annotations: Prenex*) {
    def toBinderSpec = BinderSpec(tag, x, annotations.map(_.toType): _*)
  }

  object PrenexSpec {
    def apply(spec: BinderSpec, toAvoid: Set[String]):
        (PrenexSpec, Set[String]) = spec match {
      case BinderSpec(tag, x, notes @ _*) =>
        val (prenexes, undesirables) = Prenex(notes, toAvoid)
        (PrenexSpec(tag, x, prenexes: _*), undesirables)
    }

    def apply(specs: Seq[BinderSpec], toAvoid: Set[String]):
        (Seq[PrenexSpec], Set[String]) =
      specs.foldRight[(Seq[PrenexSpec], Set[String])]((Nil, toAvoid)) {
        case (binderSpec, (specs, toAvoid)) =>
          val (spec, undesirables) = PrenexSpec(binderSpec, toAvoid)
          (spec +: specs, undesirables)
      }
  }
}
