/** Prenex forms for Existential F */
trait Prenex extends Syntax {
  case class Prenex(prefix: Seq[BinderSpec], body: Tree) {
    def toType: Tree = Prenex.bind(prefix, body)

    def flipPrefix: Seq[BinderSpec] = prefix.map({
      case BinderSpec(tag, α, notes @ _*) =>
        BinderSpec(Prenex.flip(tag), α, notes: _*)
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
    def apply(τ: Tree): Prenex =
      Prenex(τ, Set.empty[String])._1

    def apply(τ: Tree, types: Tree*): Seq[Prenex] =
      Prenex(τ +: types, Set.empty[String])._1

    def apply(τ: Tree, toAvoid: Set[String]): (Prenex, Set[String]) = {
      val (prefix, body) = τ.unbindAll(toAvoid, _ => true)
      val undesirables1 = toAvoid ++ prefix.map(_.x)
      val (pbody, undesirables2) = ofMonotype(body, undesirables1)
      (Prenex(prefix ++ pbody.prefix, pbody.body), undesirables2)
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

    def bind(prefix: Seq[BinderSpec], body: Tree): Tree =
      body.boundBy(prefix)

    def normalize(prefix: Seq[BinderSpec], body: Tree): Tree = {
      val topo = topologicalOrder(prefix)
      val specs =
        prefix.withFilter(body.freeNames contains _.x).map(
          spec => (spec, (topo(spec.x), indexOf(spec.x, body)))
        ).sortBy(_._2).map(_._1)
      bind(specs, body)
    }

    def flip(tag: Binder): Binder = tag match {
      case Universal   => Existential
      case Existential => Universal
    }

    def topologicalOrder(prefix: Seq[BinderSpec]):
        Map[String, Int] =
      topologicalOrder(prefix.map({
        case BinderSpec(_, α, note) => (α, note.freeNames)
      })(collection.breakOut): Map[String, Set[String]])

    def topologicalOrder(graph: Map[String, Set[String]]):
        Map[String, Int] = {
      var distance = -1
      var toVisit  = graph.keySet
      var result   = Map.empty[String, Int]
      while (! toVisit.isEmpty) {
        val frontier = toVisit.filter {
          α => graph(α).find(toVisit contains _) == None
        }
        if (frontier.isEmpty)
          sys error s"cycle detected"
        distance = distance +  1
        toVisit  = toVisit  -- frontier
        result   = result   ++ frontier.map(α => (α, distance))
      }
      result
    }

    // ATTRIBUTES OF A TYPE VARIABLE

    def indexOf(α: String, body: Tree): Int =
      body.preorder.indexOf(æ(α))

    // number of occurrences of α
    def count(α: String, τ: Tree): Int =
      τ.preorder.count(_ == æ(α))

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

      // only know how to recurse down to unannotated quantifications
      case τ @ ⊹(tag: Quantification, Annotation.none(), body) =>
        depth(α, body)

      case ⊹(_, _*) =>
        sys error s"depth of $α in ${τ.unparse}"
      case æ(β) if α == β =>
        0
      case _ =>
        Int.MinValue
    }
  }

  // divide the prefix of a type in prenex form
  // (wastful traversals of specs, optimization opportunity)
  case class Prefix(specs: Map[String, BinderSpec]) {
    // FIELDS

    def universal  (α: String) = tagOf(α) == Universal
    def existential(α: String) = tagOf(α) == Existential

    // maps names to tags
    def tagOf(α: String): Binder = specs(α).tag

    // debt of uncertain families down the generations
    // to be discharged when the family breaks up
    def debts(α: String) =
      ???

    def myOwnDebt(α: String): Seq[Tree] = specs(α).annotation match {
      case Annotation(_, Some(debts)) => debts
    }

    // maps children to the name of their parent
    def parent(α: String): String = specs(α).annotation match {
      case Annotation(Some(β), _) => β
    }

    // maps parent to the names of their children
    lazy val children: Map[String, Set[String]] =
      ??? /*
      specs.foldLeft(Map.empty[String, Set[String]]) {
        case (acc, PrenexSpec(tag, parent, _))
            if Seq(UniversalUncertainty, ExistentialUncertainty).
                 contains(tag) =>
          // paranoid verification of consistency:
          // parent must come before children.
          assert(! acc.contains(parent))
          acc.updated(parent, Set())
        case (acc, PrenexSpec(tag, child, Prenex(Seq(), parentNode)))
            if Seq(UniversalBound, ExistentialBound) contains tag =>
          val parent = FreeTypeVar get parentNode
          acc.updated(parent, acc(parent) + child)
        case (acc, _) =>
          acc
      }*/

    // TOOLS

    lazy val degreesOfFreedom: Set[String] = ???
    /*
      universal ++ universalChild ++
        existentialChild.filter(universalParent compose parent)
     */

    import collection.mutable.MultiMap
    case class Cache(
      children: MultiMap[String, String],
      ancestry: MultiMap[String, String],
      progeny : MultiMap[String, String])
    lazy val cache = {
      import collection.mutable.{HashMap, Set}
      val children = new HashMap[String, Set[String]]
                     with MultiMap[String, String]
      val ancestry = new HashMap[String, Set[String]]
                     with MultiMap[String, String]
      val progeny  = new HashMap[String, Set[String]]
                     with MultiMap[String, String]
      specs.foreach {
        case (α, BinderSpec(_, _, Annotation(Some(β), _))) =>
          // add the parent-child edge (β, α)
          children.addBinding(β, α)
          // all ancestors of β are ancestors of all progenies of α
          // all progenies of α are progenies of all ancestors of β
          for {
            ancestor   <- ancestry.withDefault(_ => Set.empty)(β) + β
            descendant <- progeny .withDefault(_ => Set.empty)(α) + α
          } {
            ancestry.addBinding(ancestor, descendant)
            progeny .addBinding(descendant, ancestor)
          }
        case _ =>
          ()
      }
      Cache(children, ancestry, progeny)
    }
  }

  object Prefix {
    // overloaded constructor
    def apply(linearizedPrefix: Seq[BinderSpec]): Prefix =
      Prefix(linearizedPrefix.map({
        spec => (spec.x, spec)
      })(collection.breakOut): Map[String, BinderSpec])
  }
}
