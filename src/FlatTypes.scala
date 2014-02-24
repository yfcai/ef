/** Subtype constraint resolution with ordering
  */
trait FlatTypes
    extends TypedModules with IntsAndBools with Prenex with Topology
{
  def typeCheck(m: Module):
      Either[Problem, Seq[(Option[String], Tree, Tree, Token)]] =
    ???

  case class Circular(ancestry: Ancestry)
      extends Exception(ancestry.map({
        case (a, set) =>
          "%-2s ↦ %s".format(a, set.mkString(", "))
      }).mkString("\n"))

  case class Insoluble(msg: String) extends Exception(msg)

  type Ancestry = collection.mutable.MultiMap[String, String]

  def newEmptyAncestry: Ancestry =
    new collection.mutable.HashMap[String,
      collection.mutable.Set[String]] with
        collection.mutable.MultiMap[String, String]

  class FlatTyping(module: Module)
      extends SynonymResolution(module)
  {
    typing =>
    import module._

    def isCircular(ancestry: Ancestry): Boolean =
      topologicalOrder(ancestry) match {
        case Left(_) => true
        case Right(_) => false
      }

    // resolve and quantify minimally
    def minimize(τ: Tree): Tree =
      resolve(τ)
      //quantifyMinimally(resolve(τ), Set.empty)

    def quantifyMinimally(τ: Tree, avoid: Set[String]): Tree = {
      val (prenex, newAvoid) = Prenex(τ, avoid)
      prenex.prefix.foldLeft(prenex.body) {
        case (body, BinderSpec(quantifier, x, Annotation.none())) =>
          quantifyMinimally(x, quantifier, body, newAvoid)
      }
    }

    def quantifyMinimally(
      x: String,
      quantifier: Binder,
      τ: Tree,
      avoid: Set[String]
    ): Tree =
      if (τ.freeNames contains x) {
        τ match {
          case σ0 → σ1 if ! σ1.freeNames.contains(x) =>
            →(quantifyMinimally(x, flipTag(quantifier), σ0, avoid), σ1)

          case σ0 → σ1 if ! σ0.freeNames.contains(x) =>
            →(σ0, quantifyMinimally(x, quantifier, σ1, avoid))

          case ⊹(binder: Binder,  _*) =>
            binder.unbind(τ, avoid).get match {
              case (y, Seq(Annotation.none(), body)) =>
                binder.bind(y.get, Annotation.none(),
                  quantifyMinimally(x, quantifier, body, avoid))
            }

          case τ =>
            quantifier.bind(x, Annotation.none(), τ)
        }
      }
      else
        τ

    def flipTag(tag: Binder): Binder = tag match {
      case Universal   => Existential
      case Existential => Universal
    }

    // do not quantify minimally on creation.
    // quantify minimally when adding new constraints
    // at sites of application.
    case class Inst(lhs: Tree, rhs: Tree, forebear: Option[String]) {
      def contains(α: String): Boolean =
        lhs.freeNames.contains(α) || rhs.freeNames.contains(α)

      override def toString = s"${lhs.unparse}  ⊑  ${rhs.unparse}"
    }

    type ⊑ = Inst

    object ⊑ {
      def apply(lhs: Tree, rhs: Tree, maybeForebear: Option[String]):
          Inst = Inst(lhs, rhs, maybeForebear)

      def apply(lhs: Tree, rhs: Tree, forebear: String): Inst =
        Inst(lhs, rhs, Some(forebear))

      def apply(lhs: Tree, rhs: Tree): Inst =
        Inst(lhs, rhs, None)

      def unapply(c: Inst): Option[(Tree, Tree)] =
        Some((c.lhs, c.rhs))
    }

    // minimizing lookup function
    // make sure reps are always minimized
    def lookup(x: String, gamma: Gamma): Tree =
        minimize(gamma(x))

    case class CType(
      representative: Tree,
      constraints: List[⊑],
      origin: Map[String, Tree]
    )

    // collected constraints
    case class Coll(name: String, lhs: List[Tree], rhs: List[Tree])

    // get prefix by a preorder traversal
    def getPrefix(term: Tree): List[String] = {
      val Γ = Γ0
      term.preorder.flatMap({
        case æ(α) if ! Γ.hasType(α) =>
          Some(α)
        case _ =>
          None
      }).toList
    }

    // ensure: representative is minimally quantified
    // initial value of name generator should be ABCSong
    // avoiding freenames in term
    def collect(term: Tree, gamma: Gamma, abc: ABCSong):
        CType =
      term match {
        case χ(x) =>
          // eliminate undeclared variable in a previous scan
          CType(lookup(x, gamma), Nil, Map.empty)

        case λ(x, σ0, body) =>
          val σ = minimize(σ0) // for rep.
          val CType(τ, constraints, origin) =
            collect(body, gamma.updated(x, σ), abc)
          CType(→(σ, τ), constraints, origin)

        case f ₋ x =>
          val (a, b) = (æ(abc.next), æ(abc.next))
          val CType(fType, fCons, fOrg) = collect(f, gamma, abc)
          val CType(xType, xCons, xOrg) = collect(x, gamma, abc)
          CType(
            b,
            ⊑(fType, →(a, b)) :: ⊑(xType, a) :: fCons ++ xCons,
            (fOrg ++ xOrg).updated(a.get, term).updated(b.get, term)
          )

        case Ascr(t, τ0) =>
          val τ = minimize(τ0)
          val CType(rep, cs, org) = collect(t, gamma, abc)
          CType(τ, ⊑(rep, τ) :: cs, org)
      }

    def getLoner(prefix: List[String], constraints: List[⊑]):
        Option[String] = {
      val live = prefix.filter({ α =>
        constraints.find(_ contains α) != None
      })
      live.find({ α =>
        constraints.map({
          case lhs ⊑ æ(β) if α == β => ! lhs.freeNames.contains(α)
          case æ(β) ⊑ rhs if α == β => ! rhs.freeNames.contains(α)
          case constraint => ! constraint.contains(α)
        }).min
      })
    }

    // precondition: prefix ⊆ avoid
    // @return (all, ex, broken-constraints, ancestry)
    def breakUp(
      prefix: List[String],
      constraints: List[⊑],
      avoid: Set[String],
      ancestry: Ancestry // outparam
    ): (List[String], List[String], List[⊑]) = constraints match {
      // deal with function types
      case (c @ (σ0 → σ1) ⊑ (τ0 → τ1)) :: rest =>
        val f = c.forebear
        breakUp(prefix, ⊑(τ0, σ0, f) :: ⊑(σ1, τ1, f) :: rest,
          avoid, ancestry)

      // do not break up if 1 side is a universal
      // (these are the key to typing matchList correctly! why?!)
      case (fst @ æ(α) ⊑ τ) :: rest
          if (prefix contains α) && æ(α) != τ =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid, ancestry)
        (all, ex, fst :: cs)

      case (fst @ τ ⊑ æ(α)) :: rest
          if (prefix contains α) && æ(α) != τ =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid, ancestry)
        (all, ex, fst :: cs)

      // unbind quantifiers,
      case (c @ (σ @ ⊹(binder: Binder, _*)) ⊑ τ) :: rest =>
        val (α, Seq(_, body)) = binder.unbind(σ, avoid).get
        val newC = ⊑(body, τ, α.get)
        val (all, ex, cs) =
          breakUp(
            if (binder == Universal) α.get :: prefix else prefix,
            newC :: rest, avoid + α.get,
            ancestry)

        // ancestry issue: (∀α. α → α) ⊑ (∀β. β → β)

        // ancestry by dependency
        val dep = σ.freeNames /* ++ τ.freeNames */
        dep.foreach { name =>
          ancestry.addBinding(α.get, name)
        }

        if (binder == Universal)
          (α.get :: all, ex, cs)
        else
          (all, α.get :: ex, cs)

      case (c @ σ ⊑ (τ @ ⊹(binder: Binder, _*))) :: rest =>
        val (ε, Seq(_, body)) = binder.unbind(τ, avoid).get
        val newC = ⊑(σ, body, ε.get)
        val (all, ex, cs) =
          breakUp(
            if (binder == Existential) ε.get :: prefix else prefix,
            newC :: rest, avoid + ε.get,
            ancestry)

        // ancestry by dependency
        val dep = /* σ.freeNames ++ */ τ.freeNames
        dep.foreach { name => ancestry.addBinding(ε.get, name) }

        if (binder == Existential)
          (ε.get :: all, ex, cs)
        else
          (all, ε.get :: ex, cs)

      // remove refl (interferes with loner search)
      case σ ⊑ τ :: rest if σ α_equiv τ =>
        breakUp(prefix, rest, avoid, ancestry)

      // unbreakable, e. g., ℤ  ⊑  α → β
      case fst :: rest =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid, ancestry)
        (all, ex, fst :: cs)

      case Nil =>
        (Nil, Nil, Nil)
    }

    // partition constraints with respect to a loner
    // @return (lhs, rhs, remaining-constraints)
    def partition(loner: String, cs: List[⊑]):
        (List[Tree], List[Tree], List[⊑]) = {
      val α = æ(loner)
      val lhs = cs.flatMap({
        case σ ⊑ τ if τ == α => Some(σ)
        case _ => None
      })
      val rhs = cs.flatMap({
        case σ ⊑ τ if σ == α => Some(τ)
        case _ => None
      })
      val rest = cs.filter(c => c.lhs != α && c.rhs != α)
      (lhs, rhs, rest)
    }

    // remove α-equiv entries in list of types
    def deduplicate(types: List[Tree]): List[Tree] =
      types.foldRight[List[Tree]](Nil) {
        case (τ, acc) =>
          if (acc.find(_ α_equiv τ) == None)
            τ :: acc
          else
            acc
      }

    // solve constraints up to loners
    // @return (all, ex, all-solved-variables, unsolved-constraints)
    def solve(
      all0: List[String],
      ex0: List[String],
      cs0: List[⊑],
      avoid: Set[String], // should be free variables of that term
      ancestry: Ancestry // outparam
    ): (List[String], List[String], List[Coll], List[⊑]) = {
      // 1. break up constraints
      val (all1, ex1, cs1) =
        breakUp(all0, cs0, avoid ++ all0 ++ ex0, ancestry)

      // 2. find loner
      val all2 = all1 ++ all0
      val ex2 = ex1 ++ ex0
      getLoner(all2, cs1) match {

        // 3-1. loner found.
        // procure LHS & RHS of loner.
        case Some(loner) =>
          val (lhs0, rhs0, rest) = partition(loner, cs1)

          val lhs = deduplicate(lhs0)
          val rhs = deduplicate(rhs0)

          // ancestry by dependency (loner)
          // can choose to depend on either lhs or rhs
          // not sure which one's best
          val dep = lhs
          dep.foldRight[Set[String]](Set.empty) {
            case (σ, set) => set ++ σ.freeNames
          } foreach { forebear =>
            ancestry.addBinding(loner, forebear)
          }

          val newCs = for { σ <- lhs ; τ <- rhs } yield ⊑(σ, τ, loner)
          val (all, ex, solved, unsolved) =
            solve(all2, ex2, newCs ++ rest, avoid, ancestry)
          (all, ex, Coll(loner, lhs, rhs) :: solved, unsolved)

        // 3-2. no loner exists any more
        // put remaining constraints aside for later use
        case None =>
          (all2, ex2, Nil, cs1)
      }
    }

    case class Solution(
      all      : List[String],
      ex       : List[String],
      rep      : Tree,
      coll     : List[Coll],
      origin   : Map[String, Tree],
      ancestry : Ancestry
    )

    def solve(term: Tree): Solution = {
      val CType(rep, cs, origin) =
        collect(term, Γ, new ABCSong(term.freeNames))

      // collect unquantified type variables & type variables
      // generated during constraint collection
      val all0 = getPrefix(term) ++ origin.keys

      val ancestry = newEmptyAncestry

      val (all, ex, coll, rest) =
        solve(all0, Nil, cs, term.freeNames, ancestry)
      val unsolvable = rest.filter(c => ! (c.lhs α_equiv c.rhs))
      if (! unsolvable.isEmpty)
        throw Insoluble(
          s"""|The term
              |  ${term.unparse}
              |generates unsolvable constraints
              |
              |∀${all.mkString(", ")}.
              |∃${ex.mkString(", ")}.
              |
              |${unsolvable.map(c => s"  $c").mkString("\n")}
              |
              |loner = ${getLoner(all, unsolvable)}
              |""".stripMargin)
      Solution(all, ex, rep, coll, origin, ancestry)
    }

    lazy val Γ = Γ0 ++ module.sig addTypes module.syn.keySet

    def show(term: Tree) {
      println(term.unparse)
      val Solution(all, ex, rep, coll, origin, ancestry) = solve(term)
      println()
      if (! all.isEmpty) println(s"∀${all.mkString(" ")}")
      if (!  ex.isEmpty) println(s"∃${ ex.mkString(" ")}")
      if (! all.isEmpty || ! ex.isEmpty)
        println()
      println(s"${rep.unparse}\n")
      coll.foreach {
        case Coll(α, lhs, rhs) =>
          val x   =
            if (! lhs.isEmpty)
              Array.fill(α.length)(' ').mkString
            else
              α
          val xxx = Array.fill(s"$α ⊒ ".length)(' ').mkString
          if (! lhs.isEmpty) {
            println(s"$α ⊒ ${lhs.head.unparse}")
            print(lhs.tail.map(τ => s"$xxx${τ.unparse}\n").mkString)
          }
          if (! rhs.isEmpty) {
            println(s"$x ⊑ ${rhs.head.unparse}")
            print(rhs.tail.map(τ => s"$xxx${τ.unparse}\n").mkString)
          }
          println()
      }
      println()

      origin.foreach {
        case (α, t) =>
          println(s"$α  from  ${t.unparse}")
      }

      // circularity test
      println("\nAncestry:")
      println(Circular(ancestry).getMessage)
      if (isCircular(ancestry))
        println("ERROR: Cycle detected!")
      else
        println("(not circular)")
    }

    def typeCheck(t: Tree): Boolean =
      try {
        val s = solve(t)
        ! isCircular(s.ancestry)
      }
      catch {
        case Insoluble(_) | Circular(_) =>
          false
      }
  }
}

// testbed
object FlatTypes extends FlatTypes {
  def show(files: Array[String]): Unit = files.foreach { file =>
    val module = Module.fromFile(file)
    val typing = new FlatTyping(module)
    module.naked.foreach {
      case (term, toks) =>
        typing.show(term)
    }
  }
}
