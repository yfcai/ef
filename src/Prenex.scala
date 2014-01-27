/** Prenex forms for Existential F */
trait Prenex extends Syntax with Status {
  case class Prenex(prefix: Seq[BinderSpec], body: Tree) {
    def toType: Tree = Prenex.bind(prefix, body)

    def flipPrefix: Seq[BinderSpec] = prefix.map({
      case BinderSpec(tag, α, notes @ _*) =>
        BinderSpec(Prenex.flip(tag), α, notes: _*)
    })

    def normalize: Tree =
      Prenex.normalize(prefix, body)

    // divide prefix without regard to annotations & the dependency
    // therebetwixt
    def blindPartition: (Seq[BinderSpec], Seq[BinderSpec], Tree) = {
      val (all, ex) = prefix.partition(_.tag == Universal)
      (all, ex, body)
    }

    def isUniversal(α: String): Boolean =
      prefix.find(_.x == α).map(_.tag == Universal).fold(false)(identity)

    def tagOf(α: String): Binder = prefix.find(_.x == α).get.tag

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

    /** @return (prenex, names-in-prefix-and-more) */
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


      /* TODO: DELETE ME
      case ⊹(tag, _*) =>
        sys error s"object Prenex isn't aware of $tag"

      case leaf @ ∙(_, _) =>
        (Prenex(Nil, leaf), toAvoid)
      */

      case otherwise =>
        (Prenex(Nil, otherwise), toAvoid)
    }

    def bind(prefix: Seq[BinderSpec], body: Tree): Tree =
      body.boundBy(prefix)

    // not bind unless necessary
    def close(prefix: Seq[BinderSpec], body: Tree): Tree =
      bind(prefix.filter(body.freeNames contains _.x), body)

    // HORROR: FORGOT TO TAKE INTO ACCOUNT THE ORDER OF QUANTIFIERS!
    // orderlessness makes type checker accept terms that are
    // NOT proofs in classical logic; may make system unsound
    // or inconsistent.
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
}

// prenex for prenex calculus
trait OrderlessPrenex extends Syntax with Status {
  // use the same class name on purpose so that none can mix
  // in Prenex and OrderlessPrenex at the same time
  case class Prenex(all: List[String], ex: List[String], body: Tree) {
    def toType: Tree = ∀(all, ∃(ex, body))

    lazy val usedNames: Set[String] =
      body.freeNames ++ all ++ ex
  }

  object Prenex {
    def apply(τ: Tree): Prenex =
      Prenex(τ, Set.empty[String])._1

    def apply(τ: Tree, types: Tree*): Seq[Prenex] =
      Prenex(τ +: types, Set.empty[String])._1

    /** @return (prenex, names-in-prefix-and-more) */
    def apply(τ: Tree, avoid0: Set[String]): (Prenex, Set[String]) =
      τ match {
        case α @ æ(_) =>
          (Prenex(Nil, Nil, α), avoid0)
        case σ → τ =>
          val (Prenex(all_σ, ex_σ, body_σ), avoid1) = Prenex(σ, avoid0)
          val (Prenex(all_τ, ex_τ, body_τ), avoid2) = Prenex(τ, avoid1)
          (Prenex(ex_σ ++ all_τ, all_σ ++ ex_τ, →(body_σ, body_τ)), avoid2)
        case σ @ ⊹(quantifier: Quantification, _*) =>
          quantifier.unbind(σ, avoid0) match {
            case Some((æ(α), Seq(Annotation.none(), body0))) =>
              val universal = σ.tag == Universal
              val (Prenex(all, ex, body1), avoid1) =
                Prenex(body0, avoid0 + α)
              // line break, else scala thinks the expr below is another
              // argument list of expr above.
              (Prenex(
                if (universal) α :: all else all,
                if (universal) ex else α :: ex,
                body1), avoid1)
          }
        case otherwise =>
          sys error ("orderless prenex acknowledges ∀, → but not " +
            otherwise.unparse)
      }

    def apply(types: Seq[Tree], toAvoid: Set[String]):
        (Seq[Prenex], Set[String]) =
      types.foldRight[(Seq[Prenex], Set[String])]((Nil, toAvoid)) {
        case (τ, (prenexes, toAvoid)) =>
          val (prenex, undesirables) = Prenex(τ, toAvoid)
          (prenex +: prenexes, undesirables)
      }
  }
}
