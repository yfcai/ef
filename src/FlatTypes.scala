/** Subtype constraint resolution with ordering
  */
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

    // override `resolve` to input minimally quantified types only?
    override def resolve(tau: Tree): Tree =
      if (mqFlag) {
        val x = super.resolve(tau)
        val y = quantifyMinimally(x, x.freeNames)
        if (! x.α_equiv(y))
        println(s"\n\nFOUND ${x.unparse}  !=  ${y.unparse}\n\n")
        y
      }
      else
        super.resolve(tau)

    // ensure: representative is minimally quantified
    // initial value of name generator should be ABCSong
    // avoiding freenames in term
    def collect(term: Tree, gamma: Gamma, abc: ABCSong):
        CType =
      term match {
        case χ(x) =>
          // eliminate undeclared variable in a previous scan
          CType(resolve(gamma(x)), Nil, Map.empty)

        case λ(x, σ0, body) =>
          val σ = resolve(σ0) // for rep.
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
          val τ = resolve(τ0)
          val CType(rep, cs, org) = collect(t, gamma, abc)
          CType(τ, ⊑(rep, τ) :: cs, org)

        // on type abstraction,
        // put everything inside representative,
        // including things generated so far.
        // we don't care what alpha is, so long it is something.
        // it makes sense to do this at every abstraction,
        // but it is costly,
        // so we do it once, at the marked place.
        case Λ(alpha, t) =>
          val CType(rep, cs, org) = collect(t, gamma, abc)
          // No smart-Alex pruning of constraints here.
          // Each type abstraction doubles the number of constraints.
          val degreesOfFreedom =
            cs.foldRight(rep.freeNames)(_.freeNames ++ _).toSeq
          CType(
            ∀(degreesOfFreedom, ConstrainedType(rep, cs)),
            cs, org)
      }

    def getLoner(prefix: List[String], constraints: List[Tree]):
        Option[String] = {
      val live = prefix.filter({ α =>
        constraints.find(_.freeNames contains α) != None
      })
      live.find({ α =>
        constraints.map({
          case lhs ⊑ æ(β) if α == β => ! lhs.freeNames.contains(α)
          case æ(β) ⊑ rhs if α == β => ! rhs.freeNames.contains(α)
          case constraint => ! constraint.freeNames.contains(α)
        }).min
      })
    }

    def breakBinders(
      prefix: List[String],
      css: List[Tree],
      avoid0: Set[String]
    ): (List[String], List[String], List[Tree]) = {
      val fst :: rest = css
      val σ ⊑ τ = fst
      val (p, σ0) = σ.unbindAll(avoid0, Universal, Existential)
      val avoid1 = avoid0 ++ p.map(_.x)
      val (q, τ0) = τ.unbindAll(avoid1, Universal, Existential)
      val avoid2 = avoid1 ++ q.map(_.x)

      // add things to prefix and stuff
      val accomodating =
        p.withFilter(_.tag == Universal).map(_.x) ++
        q.withFilter(_.tag == Existential).map(_.x)
      val exigent =
        p.withFilter(_.tag == Existential).map(_.x) ++
        q.withFilter(_.tag == Universal).map(_.x)

      val (all, ex, cs) = breakUp(
        prefix ++ accomodating,
        σ0 ⊑ τ0 :: rest,
        avoid2)

      (accomodating ++ all, exigent ++ ex, cs)
    }

    // precondition: prefix ⊆ avoid
    // @return (all, ex, broken-constraints, ancestry)
    def breakUp(
      prefix: List[String],
      constraints: List[Tree],
      avoid: Set[String]
    ): (List[String], List[String], List[Tree]) = constraints match {
      // deal with function types
      case (c @ (σ0 → σ1) ⊑ (τ0 → τ1)) :: rest =>
        breakUp(prefix, τ0 ⊑ σ0 :: σ1 ⊑ τ1 :: rest, avoid)

      // deal with constrained types
      case ConstrainedType(σ, cs) ⊑ τ :: rest =>
        breakUp(prefix, σ ⊑ τ :: cs.toList ++ rest, avoid)

      case σ ⊑ ConstrainedType(τ, cs) :: rest =>
        breakUp(prefix, σ ⊑ τ :: cs.toList ++ rest, avoid)

      // do not break up if 1 side is a universal
      // (these are the key to typing matchList correctly! why?!)
      case (fst @ æ(α) ⊑ τ) :: rest
          if (prefix contains α) && æ(α) != τ =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid)
        (all, ex, fst :: cs)

      case (fst @ τ ⊑ æ(α)) :: rest
          if (prefix contains α) && æ(α) != τ =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid)
        (all, ex, fst :: cs)

      // unbind quantifiers, in some order.
      case cs @ σ ⊑ τ :: rest
          if σ.tag.isInstanceOf[Binder] || τ.tag.isInstanceOf[Binder] =>
        breakBinders(prefix, cs, avoid)

      // remove refl (interferes with loner search)
      case σ ⊑ τ :: rest if σ α_equiv τ =>
        breakUp(prefix, rest, avoid)

      // unbreakable, e. g., ℤ  ⊑  α → β
      case fst :: rest =>
        val (all, ex, cs) = breakUp(prefix, rest, avoid)
        (all, ex, fst :: cs)

      case Nil =>
        (Nil, Nil, Nil)
    }

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

    // solve constraints up to loners
    // @return (all, ex, all-solved-variables, unsolved-constraints)
    def solve(
      all0: List[String],
      ex0: List[String],
      cs0: List[Tree],
      avoid: Set[String] // should be free variables of that term
    ): (List[String], List[String], List[Coll], List[Tree]) = {

      // debug session
      if (debugFlag)
        debug(all0, ex0, cs0)

      // 1. break up constraints
      val (all1, ex1, cs1) =
        breakUp(all0, cs0, avoid ++ all0 ++ ex0)

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

          val newCs = for { σ <- lhs ; τ <- rhs } yield σ ⊑ τ

          val (all, ex, solved, unsolved) =
            solve(all2, ex2, newCs ++ rest, avoid)
          (all, ex,
            Coll(loner, lhs, rhs) :: solved,
            unsolved)

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
      origin   : Map[String, Tree]
    )

    def solve(term: Tree): Solution = {
      val CType(rep, cs, origin) =
        collect(term, Γ, new ABCSong(term.freeNames))

      // collect unquantified type variables & type variables
      // generated during constraint collection
      val all0 = getPrefix(term) ++ origin.keys

      val (all, ex, coll, rest) =
        solve(all0, Nil, cs, term.freeNames)
      val unsolvable = rest.filter(c => {
        val lhs ⊑ rhs = c
        ! (lhs α_equiv rhs)
      })
      if (! unsolvable.isEmpty)
        throw Insoluble(
          s"""|The term
              |  ${term.unparse}
              |generates unsolvable constraints
              |
              |∀${all.mkString(" ")}.
              |∃${ ex.mkString(" ")}.
              |
              |${unsolvable.map(c => s"  ${c.unparse}").mkString("\n")}
              |
              |loner = ${getLoner(all, unsolvable)}
              |""".stripMargin)
      Solution(all, ex, rep, coll, origin)
    }

    lazy val Γ = Γ0 ++ module.sig addTypes module.syn.keySet

    def debug(all: List[String], ex: List[String], cs: List[Tree]) {
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
      print("next?>  ")
      System.out.flush()
      val lines = scala.io.Source.stdin.getLines
      if (lines.hasNext) {
        val line = lines.next
        if (line matches ".*[NnQq].*")
          debugFlag = false
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
      val Solution(all, ex, rep, coll, origin) = solution
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

    def wellTyped(t: Tree): Boolean =
      try { val s = solve(t) ; true }
      catch { case Insoluble(_) => false }

    def illTyped(t: Tree) = ! wellTyped(t)
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
