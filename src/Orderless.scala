/** constraint-based type checking
  * without regard for the order of quantifiers.
  * may be inconsistent, may be unsound;
  * goal is to get familiar with solving constraints.
  */
trait FirstOrderOrderlessness
    extends TypedModules with IntsAndBools
{
  var debugFlag: Boolean = false

  def typeCheck(m: Module):
      Either[Problem, Seq[(Tree, Tree, Token)]] = {
    val ord = new OrderlessTyping(m)
    ord.typeError match {
      case Some(problem) =>
        Left(problem)
      case None =>
        // can't assign type to naked expressions yet
        Right(ord.module.naked.map {
          case (t, toks) => (t, ord.YHWH, toks.head)
        })
      }
    }

  class OrderlessTyping(module: Module)
      extends SynonymResolution(module)
  {
    typing =>
    import module._

    def debugDomain(dom0: Domain, msg: String = "domain") {
      val c = Contradiction(dom0, s"DEBUGGING $msg")
      println()
      println(c.getMessage)
      var dom = breakUpConstraints(dom0)
      var i = 1
      val lines = scala.io.Source.stdin.getLines
      def prompt() {
        print("next?>  ")
        System.out.flush()
      }
      prompt
      while (lines.hasNext) {
        lines.next
        println(Contradiction(dom, s"\nafter $i step").getMessage)
        if (i % 2 == 1)
          dom = breakUpConstraints(dom) // TODO: MAKE THIS ONE STEP
        else nextDomain(dom) match {
          case Left(c) =>
            println("contradiction encountered.")
            println(c.getMessage)
            println("DEBUG OVER\n\n")
            return
          case Right(d) =>
            dom = d
        }
        i += 1
        prompt
      }

      println("\nDEBUG OVER\n\n")
    }

    def debugDefinition(name: String) {
      val t = dfn(name)
      val τ = resolve(sig(name))
      debugDomain(gatherConstraints(t, τ), s"$name = ${t.unparse}")
    }

    // INSTANTIATION CONSTRAINTS

    case object InstantiationConstraint
        extends BinaryOperator with Genus {
      val fixity: Fixity = Infixr("⊑")
      def lhs = downFrom(FunctionArrow, typeOps)
      def rhs = downFrom(FunctionArrow, typeOps)
      def opGenus = BinaryOpGenus(Type, Type, this)
    }

    case object ConstraintList extends Operator with Genus {
      val fixity: Fixity = Infixr(",") orElse CompositeItem

      def genus = this

      def tryNext = ???
      override
      def tryNextOverride: Seq[Seq[Tree]] => Seq[Seq[Operator]] =
        _ map (_ => Seq(InstantiationConstraint))

      def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)
    }

    case object ConstrainedType extends Operator {
      def genus = Type

      val fixity: Fixity = Infixl("given")
      def tryNext = Seq(
        downFrom(FunctionArrow, typeOps),
        Seq(ConstraintList))

      def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)

      def apply(τ: Tree, constraints: Seq[Tree]): Tree = {
        assert(! constraints.isEmpty) // if empty, can't unparse
        cons(τ :: ConstraintList.cons(constraints) :: Nil)
      }

      def unapply(σ: Tree): Option[(Tree, Seq[Tree])] = σ match {
        case ⊹(ConstrainedType, τ, ⊹(ConstraintList, constraints @ _*)) =>
          Some((τ, constraints))
        case _ =>
          None
      }

      override def unparse(t: Tree): String =
        s"(${super.unparse(t)})"
    }

    object ⊑ extends BinaryFactory(InstantiationConstraint)
    implicit class InstantiationConstrained(σ: Tree) {
      def ⊑ (τ: Tree) = typing.⊑(σ, τ)
    }

    case class Domain(
      prefix: List[(String, Binder)],
      constraints: List[Tree],
      representative: Tree
    ) {
      lazy val freeNames: Set[String] =
        representative.freeNames ++
          prefix.map(_._1) ++
          constraints.flatMap(_.freeNames)

      def prepend(constrained: Seq[Tree], constraints: List[Tree]):
          List[Tree] =
        constrained.foldRight(constraints) {
          case (x, xs) => x :: xs
        }

      def prepend(constrained: Tree *): Domain =
        Domain(prefix, prepend(constrained, constraints), representative)

      def adjust(x: String, tag: Binder, constrained: Tree *): Domain =
        Domain(
          (x, tag) :: prefix,
          prepend(constrained, constraints),
          representative)

      def tail: Domain =
        Domain(prefix, constraints.tail, representative)

      // a type variable is a loner if it always occur alone on
      // either side of ⊑ in all constraints
      def isLoner(x: String): Boolean =
        isLonerIn(x, constraints)

      lazy val loner: Option[(String,  Binder)] =
        prefix.find(p => isLoner(p._1))

      def isUniversal  (x: String) = typing.isUniversal  (x, prefix)
      def isExistential(x: String) = typing.isExistential(x, prefix)

      def extractLoner(x: String) = typing.extractLoner(x, constraints)

      def contradiction: Option[Contradiction] =
        typing.contradiction(this)

      // capture avoidance
      // (binder interface imposes too much overhead...)
      def avoid(names: Set[String]): Domain = {
        val clashed = prefix.flatMap {
          case (x, _) =>
            if (names contains x)
              Some(x)
            else
              None
        }
        if (clashed.isEmpty)
          this
        else {
          val fresh = ABCSong.newNames(clashed, names ++ freeNames)
          val refreshName =
            (clashed.zip(fresh).map(identity)(collection.breakOut):
                Map[String, String]
            ).withDefault(identity)
          val refreshVar =
            refreshName.map(p => (p._1, æ(p._2))).withDefault(æ.apply)
          val dom =
            Domain(
              prefix.map(p => (refreshName(p._1), p._2)),
              constraints.map(_ subst refreshVar),
              representative subst refreshVar)
          dom
        }
      }
    }

    object Domain {
      // reconstruct for terms
      def fromTerm(t: Tree): Domain =
        typing.gatherConstraints(t)

      // injection
      def injectType(τ: Tree): Domain =
        Domain(Nil, Nil, τ)

      def fromApplication(fun0: Domain, arg0: Domain): Domain = {
        val fun = fun0.avoid(arg0.freeNames)
        val arg = arg0.avoid(fun.freeNames)
        val Seq(a, b) =
          ABCSong.newNames(Seq("a", "b"), fun.freeNames ++ arg.freeNames)
        Domain(
          (a, Universal) :: (b, Universal) ::
            fun.prefix ++ arg.prefix,
          fun.representative ⊑ →(æ(a), æ(b)) ::
            arg.representative ⊑ æ(a) ::
            fun.constraints ++ arg.constraints,
          æ(b))
      }
    }

    def isLonerIn(x: String, constraints: List[Tree]): Boolean =
      if (constraints.isEmpty)
        false
      else {
        val α = æ(x)
        // loner has to BE somewhere
        constraints.find({
          case lhs ⊑ rhs =>
            lhs.freeNames.contains(x) ||
            rhs.freeNames.contains(x)
        }) != None &&
        // but he has to be there alone
        constraints.find({
          case lhs ⊑ rhs =>
          lhs != α && lhs.freeNames.contains(x) ||
          rhs != α && rhs.freeNames.contains(x)
        }) == None
      }

    case class Loneliness(lhs: List[Tree], rhs: List[Tree], rest: List[Tree])

    def extractLoner(loner: String, constraints: List[Tree]): Loneliness = {
      var lhs: List[Tree] = Nil
      var rhs: List[Tree] = Nil
      var rest: List[Tree] = Nil
      val α = æ(loner)
      constraints.reverse.foreach {
        case æ(β) ⊑ æ(γ) if β == γ =>
          // case-ID
          // do nothing if the constraint says something (not necessarily
          // the loner) instantiates to itself
          ()
        case σ ⊑ τ =>
          // because of case-ID, we'll not see "loner ⊑ loner" here.
          if (σ == α)
            rhs = τ :: rhs
          else if (τ == α)
            lhs = σ :: lhs
          else
            rest = σ ⊑ τ :: rest
      }

      // paranoid sanity check
      if (rest.length == constraints.length) sys error {
        Contradiction(
          s"problem extracting the existential loner $loner",
          Nil,
          constraints
        ).getMessage
      }

      Loneliness(lhs, rhs, rest)
    }

    def quantify(prefix: Seq[(String, Binder)], body: Tree): Tree =
      prefix.foldRight(body) {
        case ((x, binder), body) =>
          binder.bind(x, Annotation.none(), body)
      }

    // DOMAIN RECONSTRUCTION

    // Currently, no effort is expanded toward converting
    // types to prenex form.
    //
    // TODO: pull all the covariant universals to the place
    // where we want them.
    //
    // Question: what about existentials?
    // Answer: If we have a problem, then commit everything,
    // make a tag. Because it will be an example showing that
    // existentials are necessary.
    def gatherConstraints(t: Tree, τ: Tree): Domain =
      gatherConstraints(gatherConstraints(t), τ)

    def gatherConstraints(dom: Domain, τ: Tree): Domain =
      Domain(
        dom.prefix,
        dom.representative ⊑ τ :: dom.constraints,
        dom.representative)

    def gatherConstraints(term: Tree): Domain =
      gatherConstraints(
        term,
        sig.map(p => (p._1, resolve(p._2))),
        globalTypes.keySet,
        primitiveType)

    def gatherConstraints(
      term    : Tree,
      Γ       : Map[String, Tree],
      Δ       : Set[String],
      globals : PartialFunction[String, Tree]):
        Domain = term match {
      case χ(x) =>
        val τ =
          if (Γ contains x)
            Γ(x)
          else if (globals isDefinedAt x)
            globals(x)
          else
            sys error s"please discover unsub `$x` in a preliminary scan"
        Domain.injectType(resolve(τ))

      case fun ₋ arg =>
        Domain.fromApplication(
          gatherConstraints(fun, Γ, Δ, globals),
          gatherConstraints(arg, Γ, Δ, globals))

      case λ(x, σ0, body) =>
        val σ = resolve(σ0)
        val toQuantify = σ.freeNames -- Δ
        val new_Γ = Γ.updated(x, σ)
        val new_Δ = Δ ++ toQuantify
        val dom = gatherConstraints(body, new_Γ, new_Δ, globals)

        // verify internal consistency.
        // if it does not hold, then generate insoluble constraints
        dom.contradiction match {
          case None =>
            val quantifiedNames =
              toQuantify.toSeq.map(x => (x, Universal)) ++ dom.prefix

            val monotype = →(σ, dom.representative)

            val myType =
              if (dom.constraints.isEmpty)
                quantify(
                  quantifiedNames,
                  monotype)
              else
                quantify(
                  quantifiedNames,
                  ConstrainedType(monotype, dom.constraints))

            Domain(Nil, Nil, myType)

          case Some(_) =>
            val (oo, ps) = ("oo", "ps")
            val oops = æ(oo) ⊑ æ(ps)
            if (debugFlag && ! dom.constraints.contains(oops))
              debugDomain(dom, "inconsistent abstraction")

            // the abstraction is internally inconsistent.
            // generate insoluble constraints.

            Domain(
              List((oo, Existential), (ps, Existential)),
              List(oops),
              →(æ(oo), æ(ps)))
        }

      // ascription
      case Å(t, τ0) =>
        val τ = resolve(τ0)
        val dom = gatherConstraints(t, Γ, Δ, globals)
        Domain(
          dom.prefix,
          dom.representative ⊑ τ :: dom.constraints,
          τ)
    }

    def isPrefixedTypeVar(dom: Domain, x: String): Boolean =
        dom.prefix.find(_._1 == x) != None

    def shouldBreakUp(dom: Domain, τ: Tree): Boolean = τ match {
      case æ(x) if isPrefixedTypeVar(dom, x) =>
        //true // always break up: fails on matchNat
        false // never breaks up: fails on (n 0 (+ 1))
      case _ =>
        // if τ is not a type var, then it's obvious
        true // yes, do it
    }

    def flipTag(tag: Binder): Binder = tag match {
      case Universal   => Existential
      case Existential => Universal
    }

    def breakUpConstraints(dom: Domain): Domain =
      breakUpConstraints(dom, dom.freeNames)

    def breakUpConstraints(
      dom: Domain,
      avoid: Set[String]
    ): Domain =
      if (dom.constraints.isEmpty)
        dom
      else dom.constraints.head match {
        case (σ0 → τ0) ⊑ (σ1 → τ1) =>
          breakUpConstraints(dom.tail.prepend(σ1 ⊑ σ0, τ0 ⊑ τ1), avoid)

        // break up binders only if the other side isn't
        // a prefixed type variable
        case (σ0 @ ⊹(tag: Binder, _*)) ⊑ τ1
            if shouldBreakUp(dom, τ1) => // DECISION POINT
          tag.unbind(σ0, avoid) match {
            case Some((æ(x), Seq(_, τ0))) =>
              breakUpConstraints(
                dom.tail.adjust(x, tag, τ0 ⊑ τ1),
                avoid + x)
          }
        case τ0 ⊑ (σ1 @ ⊹(tag: Binder, _*))
            if shouldBreakUp(dom, τ0) => // DECISION POINT
          tag.unbind(σ1, avoid) match {
            case Some((æ(y), Seq(_, τ1))) =>
              breakUpConstraints(
                dom.tail.adjust(y, flipTag(tag), τ0 ⊑ τ1),
                avoid + y)
          }
        case ConstrainedType(τ0, constraints) ⊑ τ1 =>
          breakUpConstraints(
            dom.tail.prepend(τ0 ⊑ τ1 +: constraints: _*))
        case τ0 ⊑ ConstrainedType(τ1, constraints) =>
          breakUpConstraints(
            dom.tail.prepend(τ0 ⊑ τ1 +: constraints: _*))
        case otherwise =>
          breakUpConstraints(dom.tail, avoid ++ otherwise.freeNames).
            prepend(otherwise)
      }

    case class Contradiction(
      msg: String,
      prefix: List[(String, Binder)],
      constraints: List[Tree])
        extends Exception
    {
      override def getMessage: String =
        s"$msg\n$printPrefix$printConstraints"

      def printPrefix: String =
        if (prefix.isEmpty)
          ""
        else
          s"""${prefix.map({
            case (x, Universal  ) => s"∀$x"
            case (y, Existential) => s"∃$y"
          }).mkString(" ")}.\n"""

      def printConstraints: String =
        constraints.map({
          case σ ⊑ τ => s"  ${σ.unparse}  ⊑  ${τ.unparse}"
        }).mkString("\n")

      def isEmpty: Boolean = constraints.isEmpty
    }

    object Contradiction {
      def apply(dom: Domain, msg: String): Contradiction =
        Contradiction(msg, dom.prefix, dom.constraints)

      def apply(t: Tree, τ: Tree, msg: String):
          Contradiction =
        apply(gatherConstraints(t, τ), msg)

      def apply(t: Tree, msg: String):
          Contradiction =
        apply(gatherConstraints(t), msg)
    }

    def isExistential(x: String, prefix: List[(String, Binder)]): Boolean =
      prefix match {
        case (y, tag) :: rest if x == y =>
          tag == Existential
        case _ :: rest =>
          isUniversal(x, rest)
        case Nil =>
          false
      }

    def isUniversal(x: String, prefix: List[(String, Binder)]): Boolean =
      prefix match {
        case (y, tag) :: rest if x == y =>
          tag == Universal
        case _ :: rest =>
          isUniversal(x, rest)
        case Nil =>
          false
      }

    def verifyResolution(dom: Domain): Option[Contradiction] = {
      dom.constraints.find({ case lhs ⊑ rhs => lhs != rhs }).map {
        case σ ⊑ τ =>
          Contradiction(
            s"""|irreconciled constraint:
                |  ${σ.unparse} ⊑ ${τ.unparse}
                |""".stripMargin,
            dom.prefix, dom.constraints)
      }
    }

    def nextDomain(dom1: Domain): Either[Contradiction, Domain] =
      if (dom1.loner == None)
        Left(Contradiction("No loner left", Nil, Nil))
      else dom1.loner.get match {
        case (x, Existential) =>
          // If a loner is existential, then ⊑ relates it only to
          // itself. If anything is related via ⊑ to the loner,
          // then they have to be able to instantiate to the loner;
          // only universally quantified type variables can do that.
          // If it is true that the loner relates only to universals,
          // then proceed by identifying those universals with the
          // existential loner.
          val Loneliness(lhs, rhs, rest) =
            dom1.extractLoner(x)

          val α = æ(x)
          val unified: Map[String, Tree] = (lhs ++ rhs).map({
            case æ(y) if dom1.isUniversal(y) =>
              (y, α)
            case τ =>
              return Left(Contradiction(
                s"""|the existential $x can't be instantiated
                    |by the nonuniversal thing ${τ.unparse}
                    |""".stripMargin,
                dom1.prefix,
                dom1.constraints))
          })(collection.breakOut)
          val newConstraints = rest.map {
            case σ ⊑ τ => (σ subst unified) ⊑ (τ subst unified)
          }
          Right(Domain(
            dom1.prefix.filter(p => ! unified.contains(p._1)),
            newConstraints,
            // put representative there because we don't care
            // about it at all
            dom1.representative))
        case (x, Universal) =>
          // If a loner is universal, then it should be able to
          // instantiate to something satisfying all constraints
          // it appears in. Which happens if (in the present
          // orderlessness) and only if the contraints involving
          // it has a solution. Which happens iff every type on
          // LHS can instantiate to every type on RHS. Of course,
          // each notion of the instantiation relation ⊑ with its
          // idiosyncratic shade of orderliness must ensure satis-
          // faction of the second "iff".
          val Loneliness(lhs, rhs, rest) = dom1.extractLoner(x)
          val newConstraints: List[Tree] =
            for { σ <- lhs ; τ <- rhs } yield σ ⊑ τ
          Right(Domain(
            dom1.prefix.filter(_._1 != x),
            newConstraints ++ rest,
            // put representative there because we don't care
            // about it at all
            dom1.representative))
      }

    def contradiction(dom0: Domain): Option[Contradiction] = {
      if (dom0.constraints.isEmpty) // no constraint, no contradiction
        return None
      val dom1 = breakUpConstraints(dom0)
      if (dom1.loner == None)
        return verifyResolution(dom1)
      nextDomain(dom1).fold(Some.apply, contradiction)
    }

    def mayAscribe(dom: Domain, τ: Tree): Boolean =
      ascriptionError(dom, τ) == None

    def ascriptionError(dom: Domain, τ: Tree): Option[Contradiction] =
      gatherConstraints(dom, τ).contradiction

    def ascriptionError(t: Tree, τ: Tree, tok: Token, toks: Seq[Token]):
        Option[Problem] = {
      ascriptionError(gatherConstraints(t), τ) match {
        case None => None
        case Some(contradiction) =>

          // recompute top-level domain for debugging
          val dom = gatherConstraints(t)
          val dom1 =
            Domain(
              dom.prefix,
              dom.representative ⊑ τ :: dom.constraints,
              dom.representative)
          val con =
            Contradiction(
              s"${contradiction.getMessage}\n\nunder top-level constraints",
              dom1.prefix,
              dom1.constraints)

          Some(Problem(tok, con.getMessage))
          /* FIXME
           * Doing a preorder zip leaks de-bruijn indices.
           * fix it at Tree level.
          val problem =
            t.preorder.toSeq.zip(toks).reverse.findFirst {
              case (t, tok)
                  if t.tag == Application | t.tag == Ascription =>
                typeErrorInTerm(t, tok)
              case _ =>
                None
            }
          // problem happens at top level ascription
          if (problem == None)
            Some(Problem(tok, contradiction.getMessage))
          else
            problem
         */
      }
    }

    val YHWH = Type("∃ӭ. ӭ")

    // lacking means to reconstruct types, we test merely that
    // the term t has no internal consistencies.
    def typeErrorInTerm(t: Tree, tok: Token): Option[Problem] = {
      ascriptionError(gatherConstraints(t), YHWH) match {
        case None => None // no contradiction, no problem
        case Some(c) => Some(Problem(tok, c.getMessage))
      }
    }

    def typeErrorInDefinition(x: String): Option[Problem] =
      ascriptionError(
        dfn(x),
        resolve(sig(x)),
        dfntoks(x).head,
        getDFNTokens(dfntoks, x)).map { c => {
          if (debugFlag) debugDefinition(x)
          c
        }}

    def typeErrorInNakedExpression(t: Tree, toks: Seq[Token]):
        Option[Problem] =
      ascriptionError(t, YHWH, toks.head, toks)

    lazy val typeError: Option[Problem] =
      // TODO: discover unsigned definitions
      discoverUnknownInTypes plus
      discoverUnknownInTerms plus
      discoverUnsignedDefinitions plus {
        type T = Iterable[(Either[String, (Tree, Seq[Token])], Int)]
        val dfns: T = dfn.keys.map(x => (Left(x), dfntoks(x).head.line))
        val exps: T = naked.map(p => (Right(p), p._2.head.line))
        val stuff = (exps ++ dfns).toSeq.sortBy(_._2).map(_._1)
        stuff.findFirst {
          case Left(x) =>
            typeErrorInDefinition(x)
          case Right((t, toks)) =>
            typeErrorInNakedExpression(t, toks)
        }
      }
  }
}
