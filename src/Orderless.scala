/** constraint-based type checking
  * without regard for the order of quantifiers.
  * may be inconsistent, may be unsound;
  * goal is to get familiar with solving constraints.
  */
trait FirstOrderOrderlessness
    extends TypedModules with IntsAndBools
{
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

    // INSTANTIATION CONSTRAINTS

    case class ⊑ (lhs: Tree, rhs: Tree) {
      lazy val freeNames: Set[String] =
        lhs.freeNames ++ rhs.freeNames
    }

    implicit class InstantiationConstrained(σ: Tree) {
      def ⊑ (τ: Tree) = new ⊑(σ, τ)
    }

    case class Domain(
      prefix: List[(String, Binder)],
      constraints: List[⊑],
      representative: Tree
    ) {
      lazy val freeNames: Set[String] =
        representative.freeNames ++
          prefix.map(_._1) ++
          constraints.flatMap(_.freeNames)

      def prepend(constrained: Seq[⊑], constraints: List[⊑]): List[⊑] =
        constrained.foldRight(constraints) {
          case (x, xs) => x :: xs
        }

      def prepend(constrained: ⊑ *): Domain =
        Domain(prefix, prepend(constrained, constraints), representative)

      def adjust(x: String, tag: Binder, constrained: ⊑ *): Domain =
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
    }

    def isLonerIn(x: String, constraints: List[⊑]): Boolean =
      if (constraints.isEmpty)
        true
      else {
        val α = æ(x)
        constraints.find(c =>
          (c.lhs != α && c.lhs.freeNames.contains(x)) ||
            (c.rhs != α && c.rhs.freeNames.contains(x))) == None
      }

    case class Loneliness(lhs: List[Tree], rhs: List[Tree], rest: List[⊑])

    def extractLoner(loner: String, constraints: List[⊑]): Loneliness = {
      var lhs: List[Tree] = Nil
      var rhs: List[Tree] = Nil
      var rest: List[⊑] = Nil
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
          if (τ == α)
            lhs = σ :: lhs
        case otherwise =>
          rest = otherwise :: rest
      }
      Loneliness(lhs, rhs, rest)
    }

    object Domain {
      // reconstruct for terms
      def fromTerm(t: Tree): Domain =
        typing.gatherConstraints(t)

      // injection
      def injectType(τ: Tree): Domain =
        Domain(Nil, Nil, τ)

      def fromApplication(fun: Domain, arg: Domain): Domain = {
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
        Domain(
          dom.prefix,
          dom.constraints,
          ∀(toQuantify.toSeq: _*)(→(σ, dom.representative)))

      // ascription
      case Å(t, τ0) =>
        val τ = resolve(τ0)
        val dom = gatherConstraints(t, Γ, Δ, globals)
        Domain(
          dom.prefix,
          dom.representative ⊑ τ :: dom.constraints,
          τ)
    }

    def breakDownConstraints(dom: Domain): Domain =
      breakDownConstraints(dom, dom.freeNames)

    def flipTag(tag: Binder): Binder = tag match {
      case Universal   => Existential
      case Existential => Universal
    }

    def breakDownConstraints(
      dom: Domain,
      avoid: Set[String]
    ): Domain =
      if (dom.constraints.isEmpty)
        dom
      else dom.constraints.head match {
        case (σ0 → τ0) ⊑ (σ1 → τ1) =>
          breakDownConstraints(dom.tail.prepend(σ1 ⊑ σ0, τ0 ⊑ τ1), avoid)
        case (σ0 @ ⊹(tag: Binder, _*)) ⊑ τ1 =>
          tag.unbind(σ0, avoid) match {
            case Some((æ(x), Seq(_, τ0))) =>
              breakDownConstraints(
                dom.tail.adjust(x, tag, τ0 ⊑ τ1),
                avoid + x)
          }
        case τ0 ⊑ (σ1 @ ⊹(tag: Binder, _*)) =>
          tag.unbind(σ1, avoid) match {
            case Some((æ(y), Seq(_, τ1))) =>
              breakDownConstraints(
                dom.tail.adjust(y, flipTag(tag), τ0 ⊑ τ1),
                avoid + y)
          }
        case otherwise =>
          breakDownConstraints(dom.tail, avoid ++ otherwise.freeNames).
            prepend(otherwise)
      }

    case class Contradiction(
      msg: String,
      prefix: List[(String, Binder)],
      constraints: List[⊑])
        extends Exception
    {
      override def getMessage: String =
        s"$msg\n\nconstraints:\n$printPrefix$printConstraints"

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
    }

    def isExistential(x: String, prefix: List[(String, Binder)]): Boolean =
      ! isUniversal(x, prefix)

    def isUniversal(x: String, prefix: List[(String, Binder)]): Boolean =
      prefix match {
        case (y, tag) :: rest if x == y =>
          tag == Universal
        case _ :: rest =>
          isUniversal(x, rest)
        case Nil =>
          sys error s"can't find $x in prefix.\nprefix = $prefix"
      }

    def verifyResolution(dom: Domain): Option[Contradiction] = {
      dom.constraints.find(c => c.lhs != c.rhs).map {
        case σ ⊑ τ =>
          Contradiction(
            s"""|irreconciled constraint:
                |  ${σ.unparse} ⊑ ${τ.unparse}
                |""".stripMargin,
            dom.prefix, dom.constraints)
      }
    }

    def contradiction(dom0: Domain): Option[Contradiction] = {
      if (dom0.constraints.isEmpty) // no constraint, no contradiction
        return None
      val dom1 = breakDownConstraints(dom0)
      if (dom1.loner == None)
        return verifyResolution(dom1)
      dom1.loner.get match {
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
              return Some(Contradiction(
                s"""|the existential $x can't be instantiated
                    |by the nonuniversal thing ${τ.unparse}
                    |""".stripMargin,
                dom1.prefix, dom1.constraints))
          })(collection.breakOut)
          contradiction(Domain(
            dom1.prefix.filter(p => ! unified.contains(p._1)),
            rest,
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
          val newConstraints: List[⊑] =
            for { σ <- lhs ; τ <- rhs } yield σ ⊑ τ
          contradiction(Domain(
            dom1.prefix.filter(_._1 != x),
            newConstraints ++ rest,
            // put representative there because we don't care
            // about it at all
            dom1.representative))
      }
    }

    def mayAscribe(dom: Domain, τ: Tree): Boolean =
      ascriptionError(dom, τ) == None

    def ascriptionError(dom: Domain, τ: Tree): Option[Contradiction] =
      Domain(
        dom.prefix,
        dom.representative ⊑ τ :: dom.constraints,
        dom.representative).contradiction

    def ascriptionError(t: Tree, τ: Tree, tok: Token, toks: Seq[Token]):
        Option[Problem] = {
      ascriptionError(gatherConstraints(t), τ) match {
        case None => None
        case Some(contradiction) =>
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
        getDFNTokens(dfntoks, x))

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
