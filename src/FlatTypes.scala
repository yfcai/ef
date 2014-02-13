trait FlatTypes
    extends TypedModules with IntsAndBools with Prenex
{
  def typeCheck(m: Module):
      Either[Problem, Seq[(Option[String], Tree, Tree, Token)]] =
    ???

  class FlatTyping(module: Module)
      extends SynonymResolution(module)
  {
    typing =>
    import module._

    def minimize(τ: Tree): Tree = quantifyMinimally(τ, Set.empty)

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
    case class ⊑(lhs: Tree, rhs: Tree) {
      def contains(α: String): Boolean =
        lhs.freeNames.contains(α) || rhs.freeNames.contains(α)

      override def toString = s"${lhs.unparse}  ⊑  ${rhs.unparse}"
    }
    implicit class CreateInstantiationConstraint(lhs: Tree) {
      def ⊑ (rhs: Tree): ⊑ = new ⊑(lhs, rhs)
    }

    // minimizing lookup function
    // make sure reps are always minimized
    def lookup(x: String, gamma: Gamma): Tree =
        minimize(resolve(gamma(x)))

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
          val σ = minimize(resolve(σ0)) // for rep.
          val CType(τ, constraints, origin) =
            collect(body, gamma.updated(x, σ), abc)
          CType(→(σ, τ), constraints, origin)

        case f ₋ x =>
          val (a, b) = (æ(abc.next), æ(abc.next))
          val CType(fType, fCons, fOrg) = collect(f, gamma, abc)
          val CType(xType, xCons, xOrg) = collect(x, gamma, abc)
          CType(
            b,
            fType ⊑ →(a, b) :: xType ⊑ a :: fCons ++ xCons,
            (fOrg ++ xOrg).updated(a.get, term).updated(b.get, term)
          )
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
    def breakUp(
      constraints: List[⊑],
      avoid: Set[String]
    ): (List[String], List[String], List[⊑]) = constraints match {
      // deal with function types
      case (σ0 → σ1) ⊑ (τ0 → τ1) :: rest =>
        breakUp(τ0 ⊑ σ0 :: σ1 ⊑ τ1 :: rest, avoid)

      // unbind quantifiers,
      case ((σ @ ⊹(binder: Binder, _*)) ⊑ τ) :: rest =>
        val (α, Seq(_, body)) = binder.unbind(σ, avoid).get
        val (all, ex, cs) = breakUp(body ⊑ τ :: rest, avoid + α.get)
        if (binder == Universal)
          (α.get :: all, ex, cs)
        else
          (all, α.get :: ex, cs)

      case (σ ⊑ (τ @ ⊹(binder: Binder, _*))) :: rest =>
        val (ε, Seq(_, body)) = binder.unbind(τ, avoid).get
        val (all, ex, cs) = breakUp(σ ⊑ body :: rest, avoid + ε.get)
        if (binder == Existential)
          (ε.get :: all, ex, cs)
        else
          (all, ε.get :: ex, cs)

      // pass over things that can't be broken up
      case fst :: rest =>
        val (all, ex, cs) = breakUp(rest, avoid)
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

    // solve constraints up to loners
    // @return (all, ex, all-solved-variables, unsolved-constraints)
    def solve(
      all0: List[String],
      ex0: List[String],
      cs0: List[⊑],
      avoid: Set[String] // should be free variables of that term
    ): (List[String], List[String], List[Coll], List[⊑]) = {
      // 1. break up constraints
      val (all1, ex1, cs1) = breakUp(cs0, avoid ++ all0 ++ ex0)

      // 2. find loner
      val all2 = all1 ++ all0
      val ex2 = ex1 ++ ex0
      getLoner(all2, cs1) match {

        // 3-1. loner found.
        // procure LHS & RHS of loner.
        case Some(loner) =>
          val (lhs, rhs, rest) = partition(loner, cs1)
          val newCs = for { σ <- lhs ; τ <- rhs } yield σ ⊑ τ
          val (all, ex, solved, unsolved) =
            solve(all2, ex2, newCs ++ rest, avoid)
          (all, ex, Coll(loner, lhs, rhs) :: solved, unsolved)

        // 3-2. no loner exists any more
        // put remaining constraints aside for later use
        case None =>
          (all2, ex2, Nil, cs1)
      }
    }

    case class Solution(
      all    : List[String],
      ex     : List[String],
      rep    : Tree,
      coll   : List[Coll],
      origin : Map[String, Tree]
    )

    def solve(term: Tree): Solution = {
      val CType(rep, cs, origin) =
        collect(term, Γ, new ABCSong(term.freeNames))

      // collect unquantified type variables & type variables
      // generated during constraint collection
      val all0 = getPrefix(term) ++ origin.keys

      val (all, ex, coll, rest) = solve(all0, Nil, cs, term.freeNames)
      val unsolvable = rest.filter(c => ! (c.lhs α_equiv c.rhs))
      if (! unsolvable.isEmpty)
        sys error s"""|The term
                      |  ${term.unparse}
                      |generates unsolvable constraints
                      |${unsolvable.map(c => s"  $c").mkString("\n")}
                      |""".stripMargin
      Solution(all, ex, rep, coll, origin)
    }

    lazy val Γ = Γ0 ++ module.sig addTypes module.syn.keySet

    def show(term: Tree) {
      println(term.unparse)
      val Solution(all, ex, rep, coll, origin) = solve(term)
      println()
      if (! all.isEmpty) println(s"∀${all.mkString(" ")}")
      if (!  ex.isEmpty) println(s"∃${ ex.mkString(" ")}")
      if (! all.isEmpty || ! ex.isEmpty)
        println()
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
