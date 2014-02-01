trait SystemF extends TypedModules
    with IntsAndBools with Status with Aliasing with Topology
{
  def typeCheck(module: Module):
      Either[Problem, Seq[(Option[String], Tree, Tree, Token)]] = {

    val human = new SystemFTyping(module)

    // compute type of definitions without signatures
    human.instrumentality match {
      case Left(problem) =>
        Left(problem)

      case Right(world) =>
        // check definitions *after* instrumentality to not
        // forbid mutual recursion
        world.typeCheck
    }
  }

  class SystemFTyping(m0: Module) extends SynonymResolution(m0) {
    // precondition: m0 has been instrumented, all definitions
    // have an accompanying signature
    def typeCheck:
        Either[Problem, Seq[(Option[String], Tree, Tree, Token)]] = {
      import m0._

      // sort definitions & naked expressions by line numbers
      val entities =
        (dfn.map({ case (x, xdef) => (Some(x), xdef, dfntoks(x)) })
          ++ naked.map({ case (e, toks) => (None, e, toks) })).
          toSeq.sortBy(_._3.head.line)

      Right(entities.map {
        case (name, t, toks) => getType(t, toks) match {
          case Left(problem) =>
            return Left(problem)

          case Right(actual) =>
            val τ =
              if (name == None)
                actual
              else {
                val x = name.get
                val declared = m0.sig(x)
                if (! (resolve(declared) α_equiv actual)) {
                  return Left(Problem(
                    m0.dfntoks(x).head,
                    s"""|type mismatch.
                        |declared: ${declared.unparse}
                        |actual  : ${actual.unparse}
                        |""".stripMargin))
                }
                declared
              }
            (name, t, τ, toks.head)
        }
      })
    }

    // the completion of humanity and the purification of souls
    def instrumentality: Either[Problem, SystemFTyping] = {
      // an outcast is a definition without type signature
      val outcasts = m0.dfn.filterNot(m0.sig contains _._1)

      // order outcasts by topological order if possible
      val graph: Map[String, Set[String]] =
        outcasts.map(p => (p._1, p._2.freeNames))(collection.breakOut)
      val topology = topologicalOrder(graph) match {
        case Left(baddies) =>
          return Left(Problem(
            m0.dfntoks(baddies.head).head,
            s"""|circular definitions need type signatures:
                |  ${baddies mkString ", "}""".stripMargin))
        case Right(topo) =>
          topo
      }
      val sortedOutcasts = outcasts.map(p => (p, topology(p._1))).
        toSeq.sortBy(_._2).map(_._1)

      // compute the type of each outcast
      // (includes redundant synonym resolution)
      val lcl = sortedOutcasts.foldLeft(m0) {
        case (module, (x, xdef)) =>
          new SystemFTyping(module).getType(xdef, m0.dfntoks(x)) match {
            case Left(problem) =>
              return Left(problem)
            case Right(τ) =>
              module.add(⊹(Signature, χ(x), τ), m0.dfntoks(x))
          }
      }

      Right(new SystemFTyping(lcl))
    }

    def Γ = Γ0 ++ m0.sig addTypes m0.syn.keySet

    def getType(t: Tree, toks: Seq[Token]): Either[Problem, Tree] = {
      getType(Γ, t) match {
        case Success(τ) =>
          Right(τ)

        case Failure(_) =>
          Left(t.blindPreorder.toSeq.zip(toks).reverse.findFirst({
            case ((t, gamma), tok) if t.tag.genus == Term =>
              getType(Γ ++ gamma, t) match {
                case Success(_) =>
                  None
                case Failure(report) =>
                  Some(Problem(tok, report))
              }
            case _ =>
              None
          }).get)
      }
    }

    def getType(Γ: Gamma, t: Tree): Status[Tree] = t match {
      case χ(x) =>
        if (Γ contains x)
          Success(resolve(Γ(x)))
        else
          Failure(s"undeclared identifier $x")

      case λ(x, σ, body) =>
        val badTypes = Γ.badTypes(σ.freeNames)
        if (! badTypes.isEmpty)
          Failure(s"""|undeclared type variables in argument type annotation:
                      |  ${badTypes.mkString(", ")}""".
            stripMargin)
        else
          getType(Γ.updated(x, σ), body).flatMap(
            τ => Success(→(resolve(σ), τ)))

      case f ₋ x =>
        for {
          functionType <- getType(Γ, f)
          _ <- NoReturn
        } yield functionType match {
          case σ → τ =>
            for { σ0 <- getType(Γ, x) ;  _ <- NoReturn } yield
              if (σ0 α_equiv σ)
                Success(τ)
              else
                Failure(
                  s"""|operand type mismatch. operator expects
                      |  ${σ.unparse}
                      |but operand has type
                      |  ${σ0.unparse}
                      |""".stripMargin)
          case nonfunction => Failure(
            s"nonfunction in operator position: ${nonfunction.unparse}")
        }

      case Λ(α, t) => {
        val Γα = Γ.addType(α)
        for { τ <- getType(Γα, t) } yield ∀(α, Annotation.none(), τ)
      }

      case t □ σ => {
        val badTypes = Γ.badTypes(σ.freeNames)
        if (! badTypes.isEmpty)
          Failure(s"""|undeclared type variables when instantiating it:
                      |  ${badTypes.mkString(", ")}""".
            stripMargin)
        else
          for { τ <- getType(Γ, t) ; _ <- NoReturn } yield τ.tag match {
            case Universal => Success(τ(resolve(σ)))
            case otherwise => Failure(
              s"cannot instantiate nonuniversal type ${τ.unparse}")
          }
      }
    }
  }
}
