/** Nuclear Football Megaslave */
trait FlatTypes
    extends TypedModules with IntsAndBools with Prenex with Topology
       with MinimalQuantification
       with ConstrainedTypes
{
  // if ill-typed, throw tantrum.
  def typeCheck(m: Module):
      Either[Problem, Seq[(Option[String], Tree, Tree, Token)]] = {
    val typing = new FlatTyping(m)
    import m._
    import typing._
    dfn.foreach {
      case (x, xdef) =>
        if (illTyped(Ascr(xdef, sig(x))))
          sys error s"ill typed definition: $x"
    }
    Right(naked.map {
      case (t, tok :: _) =>
        if (illTyped(t))
          sys error s"${tok.fileLine} ill typed naked expression"
        (None, t, YHWH, tok)

      case _ =>
        sys error "an unanticipated catastrophe"
    })
  }

  override lazy val termOps: List[Operator] =
    List(
      PolymorphismMarker,
      AnnotatedAbstraction,
      IfThenElse,
      Ascription,
      Instantiation,
      Application,
      ParenthesizedTerm,
      FreeVar)

  // polymorphism marker
  case object PolymorphismMarker extends Operator {
    def genus = Term
    def symbol = Seq("Λ", """\polymorphic""")

    override def precondition(items: Seq[Tree]): Boolean =
      items.length > 2 &&
      fixity.hasBody(items.head, symbol) &&
      fixity.hasBody(items.tail.head, ".")

    val fixity: Fixity = new Fixity {
      def splits(items: Items): Iterator[ItemGroups] =
        Iterator(Seq(items drop 2))
    }

    def tryNext: Seq[Seq[Operator]] = Seq(termOps)

    def cons(children: Seq[Tree]): Tree = ⊹(this, children.head)

    override def unparse(t: Tree): String = t match {
      case ⊹(tag, body) if tag == this =>
        s"Λ. ${body.unparse}"
    }
  }

  type Dependency = collection.immutable.HashMap[String, Set[String]]
  type Source = Map[String, Src]
  type Bounds = List[(String, Bds)]
  type Forbidden = Map[String, List[String]] // maps exigents to things that can't depend on them

  case class Src(origin: Tree, antagonist: Tree)

  case class Bds(lower: List[Tree], upper: List[Tree]) {
    lazy val fv: Set[String] =
      lower.foldRight(Set.empty[String])(_.freeNames ++ _) ++
      upper.foldRight(Set.empty[String])(_.freeNames ++ _)
  }

  /** @param source set of type variables we care about
    * @param bounds instantiations of all accomodating variables
    * @return instantiations we care about
    *
    * precondition: bounds is sorted in reverse dependency order
    * (is satisfied if each use S-Loner prepends the loner's instantiation)
    */
  def trace(source: Set[String], bounds: Bounds): Bounds = bounds match {
    case (a, bds) :: tail if source contains a =>
      (a, bds) :: trace(source ++ bds.fv, tail)

    case _ :: tail =>
      trace(source, tail)

    case Nil =>
      Nil
  }

  def emptyDependency: Dependency = collection.immutable.HashMap.empty
  def emptyBounds: Bounds = Nil

  // absoluteFlag: if set, insert polymorphism markers everywhere
  def absoluteFlag: Boolean = ! manualFlag

  // get all type variables in annotations of AnnotatedAbstraction
  // INCLUDING global names
  def allFreeNamesInAnnotations(term: Tree): Set[String] = term match {
    //case ⊹(PolymorphismMarker, _*) =>
    //  Set.empty
    //
    // do not skip subterms under polymorphism markers.
    // if constraint generator does things correctly,
    // then names that should not be bound are not free already.

    case λ(x, sigma, body) =>
      sigma.freeNames ++ allFreeNamesInAnnotations(body)

    case ⊹(tag, children @ _*) =>
      children.foldRight(Set.empty[String])((t, s) => allFreeNamesInAnnotations(t) ++ s)

    case ∙(_, _) =>
      Set.empty
  }

def annotatedUntilNextPolyMarker(term: Tree): Set[String] = term match {
    case ⊹(PolymorphismMarker, _*) =>
      Set.empty

    case λ(x, sigma, body) =>
      sigma.freeNames ++ allFreeNamesInAnnotations(body)

    case ⊹(tag, children @ _*) =>
      children.foldRight(Set.empty[String])((t, s) => allFreeNamesInAnnotations(t) ++ s)

    case ∙(_, _) =>
      Set.empty
  }

  val YHWH = Type("∃i. i")

  case class Insoluble(msg: String) extends Exception(msg)

  class FlatTyping(module: Module)
      extends SynonymResolution(module)
  {
    typing =>
    import module._

    case class CType(
      representative: Tree,
      constraints: List[Tree],
      origin: Map[String, Tree]
    )

    // collected constraints
    case class Coll(name: String, lhs: List[Tree], rhs: List[Tree])

    // ensure: representative is minimally quantified
    // initial value of name generator should be ABCSong
    // avoiding freenames in term
    def collect(term: Tree, gamma: Gamma, abc: ABCSong):
        CType = term match {
      case χ(x) =>
        // eliminate undeclared variable in a previous scan
        CType(resolve(gamma(x)), Nil, Map.empty)

      case λ(x, σ0, body) =>
        if (absoluteFlag) {
          val σ = resolve(σ0)
          val newTypeVars = σ.freeNames -- gamma.types
          val CType(τ, cs, origin) =
            collect(body, gamma.updated(x, σ).addTypes(newTypeVars), abc)
          val rep = →(σ, τ)
          val degreesOfFreedom =
            (cs.foldRight(rep.freeNames)(_.freeNames ++ _) -- gamma.types).toSeq
          val newRep = if (cs.isEmpty) rep else ConstrainedType(rep, cs)
          CType(
            ∀(degreesOfFreedom, newRep),
            if (nodupeFlag) Nil else cs,
            origin)
        }
        else {
          val σ = resolve(σ0) // for rep.
          val CType(τ, constraints, origin) =
            collect(body, gamma.updated(x, σ).addTypes(σ.freeNames), abc)
          CType(→(σ, τ), constraints, origin)
        }

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
        val τ = resolve(τ0)
        val CType(rep, cs, org) = collect(t, gamma, abc)
        CType(τ, ⊑(rep, τ) :: cs, org)

      // on polymorphism marker,
      // solve all constraints generated so far,
      // then put solution in a constrained type.
      // this should prevent nontermination on omega.
      case ⊹(PolymorphismMarker, t) =>
        if (absoluteFlag)
          collect(t, gamma, abc)
        else {
          val newGamma = gamma addTypes annotatedUntilNextPolyMarker(t)
          val ct = collect(t, newGamma, abc)
          val CType(rep, cs, org) = ct
          val (accomodating, exigent, free) = getPrefix(t, ct)
          val psol =
            solve(accomodating, exigent, cs,
              t.freeNames,
              Map.empty, Map.empty)
          val soln = Solution(ct, psol)

          // paranoidly check for circular insanity
          // (if getLoner is correct, then soln should be sane)
          if (! isSane(soln))
            throw new Insoluble(s"irresolvable subterm: ${term.unparse}")

          // trace relevant instantiations.
          // all accomodating variables are traced except those
          // eliminated by S-Refl (as opposed to S-Loner)
          val instantiations = trace(rep.freeNames, soln.bounds)

          // could be computed during tracing. chose not to, so that
          // `trace` has a simpler interface
          val relevantNames = instantiations.foldRight(rep.freeNames)(_._2.fv ++ _)

          val finalAcc = soln.all.filter(relevantNames)
          val finalExi = soln.ex.filter(relevantNames)

          val resolvedConstraints: List[Tree] = instantiations.flatMap({
            case (a, bds) =>
              bds.lower.map(_ ⊑ æ(a)) ++ bds.upper.map(æ(a) ⊑ _)
          })(collection.breakOut)

          if (resolvedConstraints.isEmpty)
            CType(∀(finalExi ++ finalAcc, rep),
              Nil,
              org)
          else
            CType(
              ∀(finalExi ++ finalAcc, ConstrainedType(rep, resolvedConstraints)),
              Nil,
              org)
        }
    }

    def getLoner(prefix: List[String], constraints: List[Tree], forbidden: Forbidden):
        Option[String] = {
      val live = prefix.filter({ α =>
        constraints.find(_.freeNames contains α) != None
      })
      // prefer elder loners
      live.reverse.find({ α =>
        constraints.map({
          case lhs ⊑ æ(β) if α == β =>
            ! lhs.freeNames.contains(α) && permissible(lhs.freeNames, α, forbidden)

          case æ(β) ⊑ rhs if α == β =>
            ! rhs.freeNames.contains(α) && permissible(rhs.freeNames, α, forbidden)

          case constraint =>
            ! constraint.freeNames.contains(α)
        }).min
      })
    }

    /** @param dependency names in the bounds of an accomodating variable
      * @param accomodating the loner
      * @param forbidden mapping each exigent to variables quantified before it
      * @return whether the dependency is permissible
      */
    def permissible(dependency: Set[String], accomodating: String, forbidden: Forbidden): Boolean =
      None == dependency.find( exigent =>
        forbidden.andThen(_ contains accomodating).applyOrElse[String, Boolean](exigent, _ => false)
      )

    case class Broken(
      accomodating: List[String],
      exigent: List[String],
      constraints: List[Tree],
      source: Source,
      forbidden: Forbidden
    ) {
      def prepend(constraint: Tree): Broken =
        copy(constraints = constraint :: constraints)

      def add(theSource: Source): Broken =
        copy(source = theSource)
    }

    object Broken {
      val empty: Broken = Broken(Nil, Nil, Nil, Map.empty, Map.empty)
    }

    def breakBinders(
      prefix: List[String],
      css: List[Tree],
      avoid0: Set[String],
      source: Source
    ): Broken = {
      val fst :: rest = css
      val σ ⊑ τ = fst
      val (p, σ0) = σ.unbindAll(avoid0, Universal, Existential)
      val avoid1 = avoid0 ++ p.map(_.x)
      val (q, τ0) = τ.unbindAll(avoid1, Universal, Existential)
      val avoid2 = avoid1 ++ q.map(_.x)

      val pu = p.withFilter(_.tag == Universal).map(_.x)
      val qu = q.withFilter(_.tag == Universal).map(_.x)

      // ensure that no existentials exist
      assert(pu.length == p.length)
      assert(qu.length == q.length)

      // add things to prefix and stuff
      // (remember that pe and qe are empty)
      val accomodating = pu
      val exigent      = qu

      // track origins and antagonists
      val src0: Source =
        (p.map(_.x -> Src(σ, τ))(collection.breakOut): Source) ++
        (q.map(_.x -> Src(τ, σ)))

      val Broken(all, ex, cs, src1, fbd1) = breakUp(
        prefix ++ accomodating,
        σ0 ⊑ τ0 :: rest,
        avoid2,
        source ++ src0
      )

      Broken(
        accomodating ++ all,
        exigent ++ ex,
        cs,
        src1,
        if (prefix.isEmpty) fbd1 else fbd1 ++ qu.map(_ -> prefix)
      )
    }

    // precondition: prefix ⊆ avoid
    // @return (all, ex, broken-constraints, ancestry)
    def breakUp(
      prefix: List[String],
      constraints: List[Tree],
      avoid: Set[String],
      source: Source
    ): Broken = constraints match {
      // deal with function types
      case (c @ (σ0 → σ1) ⊑ (τ0 → τ1)) :: rest =>
        breakUp(prefix, τ0 ⊑ σ0 :: σ1 ⊑ τ1 :: rest, avoid, source)

      // deal with constrained types
      // constrained type will never happen on RHS
      case ConstrainedType(σ, cs) ⊑ τ :: rest =>
        breakUp(prefix, σ ⊑ τ :: cs.toList ++ rest, avoid, source)

      // do not break up if 1 side is a universal
      // (these are the key to typing matchList correctly! why?!)
      // (these make typing omega nonterminating)

      case (fst @ æ(α) ⊑ τ) :: rest
          if (prefix contains α) && æ(α) != τ =>
        breakUp(prefix, rest, avoid, source) prepend fst

      case (fst @ τ ⊑ æ(α)) :: rest
          if (prefix contains α) && æ(α) != τ =>
        breakUp(prefix, rest, avoid, source) prepend fst


      // unbind quantifiers, in some order.
      case cs @ σ ⊑ τ :: rest
          if (σ.tag.isInstanceOf[Binder] || τ.tag.isInstanceOf[Binder]) &&
             shouldBreakUp(σ, τ, source) =>
        breakBinders(prefix, cs, avoid, source)

      // remove refl (interferes with loner search)
      case σ ⊑ τ :: rest if σ α_equiv τ =>
        breakUp(prefix, rest, avoid, source)

      // unbreakable, e. g., ℤ  ⊑  α → β
      case fst :: rest =>
        breakUp(prefix, rest, avoid, source) prepend fst

      case Nil =>
        Broken.empty.add(source)
    }

    // can break up possible binders if no free variable in τ is
    // generated by σ.
    //
    // trying to avoid nontermination of type checking by this.
    def shouldBreakUp(σ: Tree, τ: Tree, source: Source): Boolean = true
    /* obsolete
      None == τ.freeNames.find({ k =>
        // resorting to pointer equality...
        source.contains(k) && source(k).origin.eq(σ)
      })
     */

    // partition constraints with respect to a loner
    // @return (lhs, rhs, remaining-constraints)
    def partition(loner: String, cs: List[Tree]):
        (List[Tree], List[Tree], List[Tree]) = {
      val α = æ(loner)
      val lhs = cs.flatMap({
        case c @ σ ⊑ τ if τ == α => Some(σ)
        case _ => None
      })
      val rhs = cs.flatMap({
        case c @ σ ⊑ τ if σ == α => Some(τ)
        case _ => None
      })
      val rest = cs.filter(c => {
        val lhs ⊑ rhs = c
        lhs != α && rhs != α
      })
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

    // partial solution
    case class PSol(
      all: List[String],
      ex: List[String],
      solved: List[Coll],
      unsolved: List[Tree],
      source: Source,
      dependency: Dependency,
      bounds: Bounds,
      forbidden: Forbidden
    )

    // solve constraints up to loners
    // @return (all, ex, all-solved-variables, unsolved-constraints)
    def solve(
      all0: List[String],
      ex0: List[String],
      cs00: List[Tree],
      avoid: Set[String], // should be free variables of that term
      source: Source,
      forbidden: Forbidden
    ): PSol = {
      // debug session
      if (debugFlag)
        debug(all0, ex0, cs00, source, forbidden)

      // 0. eliminate duplicates
      val cs0 = cs00.filterNot { case σ ⊑ τ => σ α_equiv τ }

      // 1. break up constraints
      val Broken(all1, ex1, cs1, src1, fbd1) =
        breakUp(all0, cs0, avoid ++ all0 ++ ex0, source)

      // 2. find loner
      val all2 = all1 ++ all0
      val ex2 = ex1 ++ ex0
      val fbd2 = forbidden ++ fbd1
      getLoner(all2, cs1, fbd2) match {

        // 3-1. loner found.
        // procure LHS & RHS of loner.
        case Some(loner) =>
          val (lhs0, rhs0, rest) = partition(loner, cs1)

          val lhs = deduplicate(lhs0)
          val rhs = deduplicate(rhs0)

          // track dependencies
          val dep1: Dependency = emptyDependency ++ (
            for {
              tau <- lhs ++ rhs
              exigent <- tau.freeNames
              // track dependencies only of the exigent
              if ex2 contains exigent
            }
            yield (exigent, Set(loner))
          )

          val newCs = for { σ <- lhs ; τ <- rhs } yield σ ⊑ τ

          val PSol(all, ex, solved, unsolved, src3, dep3, bds3, fbd3) =
            solve(all2, ex2, newCs ++ rest, avoid, src1, fbd2)
          PSol(all, ex,
            Coll(loner, lhs, rhs) :: solved,
            unsolved,
            src3,
            dep1.merged(dep3)((p, q) => (p._1, p._2 ++ q._2)),
            (loner, Bds(lhs, rhs)) :: bds3,
            fbd1 ++ fbd3
          )

        // 3-2. no loner exists any more
        // put remaining constraints aside for later use
        case None =>
          PSol(all2, ex2, Nil, cs1, src1, emptyDependency, emptyBounds, fbd1)
      }
    }

    case class Solution(
      all        : List[String],
      ex         : List[String],
      rep        : Tree,
      coll       : List[Coll],
      origin     : Map[String, Tree],
      source     : Source,
      dependency : Dependency,
      bounds     : Bounds,
      forbidden  : Forbidden
    )

    object Solution {
      def apply(ct: CType, psol: PSol): Solution = {
        val CType(rep, cs, origin) = ct

        val PSol(all, ex, coll, rest, src, dep, bds, fbd) = psol
          val unsolvable = rest.filter(c => {
            val lhs ⊑ rhs = c
            ! (lhs α_equiv rhs)
          })

        // failure at constraint solving signaled by exception thrown
        // when converting PSol to Solution.

        if (! unsolvable.isEmpty)
          throw Insoluble(
            s"""|unsolvable constraints
                |
                |∀${all.mkString(" ")}.
                |∃${ ex.mkString(" ")}.
                |
                |${unsolvable.map(c => s"  ${c.unparse}").mkString("\n")}
                |
                |loner = ${getLoner(all, unsolvable, fbd)}
                |""".stripMargin)
        Solution(all, ex, rep, coll, origin, src, dep, bds, fbd)
      }
    }

    def solve(term: Tree): Solution = {
      val ctype @ CType(rep, cs, origin) =
        collect(term, Γ, new ABCSong(term.freeNames))

      // collect unquantified type variables & type variables
      // generated during constraint collection
      val (all0, ex0, free) = getPrefix(term, ctype)

      Solution(ctype, solve(all0, ex0, cs, term.freeNames, Map.empty, Map.empty)) // TODO: need to avoid `free` here?
    }

    // @param term the term from which constraints are generated
    // @param cs the generated constraints CType(rep, cs, origin)
    // @return (accomodating-type-variables, exigent-type-variables, free-type-variables-in-rep-and-cs)
    def getPrefix(term: Tree, ct: CType): (List[String], List[String], Set[String]) = {
      val CType(rep, cs, origin) = ct
      val free = cs.map(_.freeNames).foldRight(rep.freeNames)(_ ++ _) -- Γ.types
      val exigent = allFreeNamesInAnnotations(term).filter(free)
      val accomodating = free -- exigent
      (accomodating.toList, exigent.toList, free)
    }

    lazy val Γ = Γ0 ++ module.sig addTypes module.syn.keySet

    def debug(all: List[String], ex: List[String], cs: List[Tree], source: Source, forbidden: Forbidden) {
      println()
      if (! all.isEmpty) {
        println(s"∀ ${all.mkString(" ")}")
        println()
      }
      if (! ex.isEmpty) {
        println(s"∃ ${ ex.mkString(" ")}")
        println()
      }
      println(cs.map("  " + _.unparse).mkString("\n\n"))
      println()

      // print source of free vars
      val free = cs.foldRight(Set.empty[String])(_.freeNames ++ _)
      free.foreach {
        case a if forbidden contains a =>
          println(s"  $a after ${forbidden(a).mkString(" ")}")

        case _ =>
          ()
      }
      println()

      print("next?>  ")
      System.out.flush()
      val lines = scala.io.Source.stdin.getLines
      if (lines.hasNext) {
        val line = lines.next
        if (line matches ".*[Nn].*")
          debugFlag = false
        else if (line matches ".*[Qq].*")
          sys error "aborted"
      }
      else
        debugFlag = false
    }

    def show(term: Tree) {
      println(term.unparse)
      val solution = solve(term)
      show(solve(term))
    }

    def show(solution: Solution) {
      val Solution(all, ex, rep, coll, origin, src, dep, bds, fbd) = solution
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
    }

    // calls isSane to check for quantifier ordering violation
    // just in case
    def wellTyped(t: Tree): Boolean =
      try { val s = solve(t) ; isSane(s) }
      catch { case Insoluble(_) => false }

    def illTyped(t: Tree) = ! wellTyped(t)

    def isSane(s: Solution): Boolean = {
      for {
        e <- s.ex

        if s.dependency contains e

        // test if there is no dependent accomodating variable
        // present by the time an exigent variable is involved in an S-RI.
        a <- s.dependency(e)

        // alternatively, we may trace transitive descendants.
        // the universals ain't so loopless right now,
        // so if we include them in the dependency tracker,
        // they mess things up.
        // a <- strictDescendants(e, s.dependency)

        if s.forbidden.andThen(_ contains a).applyOrElse[String, Boolean](e, _ => false)
      } {
        println(s"reverse dependency: $e determines $a")
        return false
      }
      true
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
