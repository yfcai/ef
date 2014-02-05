object Experiments extends Flags {
  val onTrial: Experiment =
    DepthFirstSearchExperiment

  val experiments = List[Experiment](
    DepthFirstSearchExperiment,
    AbsLocationExperiment,
    TypeApplicationExperiment,
    OrderlessExperiment,
    MatchNatExperiment,
    DesugarExperiment,
    EFStringExperiment,
    CaptureExperiment,
    NondeterminismExperiment,
    UnificationExperiment,
    PrenexExperiment,
    DeclarationsExperiment,
    AnnotationExperiment,
    AlphaEquivExperiment,
    TypeListExperiment,
    FileParsingExperiment,
    CStyleConditionalExperiment,
    AbstractionsExperiment,
    SourceLocationExperiment,
    ShadowyExperiment,
    AnnotatedBinderExperiment,
    CollapsedBinderExperiment,
    AtomListExperiment,
    AscriptionExperiment,
    FunctionArrowExperiment,
    ApplicationExperiment,
    SelfReferenceExperiment,
    ProtoASTExperiment).reverse

  val lookup: Map[String, Experiment] =
    (onTrial +: experiments).
      map(e => (e.toString, e))(collection.breakOut)

  def maintenance() = experiments foreach { ex =>
    ex.copyFlags(this)
    if (!ex.verify) sys error s"failed: $ex"
  }

  def run(args: Array[String], debug: Boolean): Unit =
    if (args.isEmpty) {
      run(onTrial, debug)
      println("MAINTAINING ...")
      maintenance()
      println("MAINTENANCE SUCCESSFUL")
    }
    else args.foreach { exp =>
      lookup.get(exp).fold({
        System.err.println(s"${exp}Experiment: nonexistent")
        return
      })(e => runAndVerify(e, debug))
    }

  def run(which: Experiment, debug: Boolean): Unit = {
    which.copyFlags(this)
    if (debug)
      which.debug
    else
      which.trial
  }

  def runAndVerify(which: Experiment, debug: Boolean) {
    run(which, debug)
    if(! which.verify) {
      run(which, true)
      System.err.
        println("[Debug mode triggered because verification failed]")
    }
  }

  trait Experiment extends Flags {
    override def toString: String = {
      val fullname = getClass.getName
      val classname = fullname.substring(fullname.lastIndexOf('.') + 1)
      val outername = if (classname.endsWith("$"))
        classname.init
      else
        classname
      val simplename = outername.substring(outername.lastIndexOf('$') + 1)
      val experiment = "Experiment"
      if (simplename endsWith experiment)
        simplename.substring(0, simplename.length - experiment.length)
      else
        simplename
    }

    def run: String
    def expected: String = "UNEXPECTED"

    def verify: Boolean = {
      // always produce unicode during verification
      val unicode = unicodeFlag
      unicodeFlag = true
      val result = run == expected
      unicodeFlag = unicode
      result
    }

    def trial(): Unit = print(run)

    def debug(): Unit = {
      val (actual, expect) = (run, expected)
        (actual.lines.toSeq, expect.lines.toSeq).zipped foreach {
          case (lhs, rhs) =>
            println(lhs == rhs)
            println(lhs + "$")
            println(rhs + "$\n")
        }
      println(s"actual length = ${actual.length}")
      println(s"expect length = ${expect.length}")
    }

    val stream = new collection.mutable.StringBuilder

    def puts(s: Any = "") = { put(s) ; stream += '\n' }
    def put(s: Any) = stream ++= s.toString

    def dump(): String = {
      val result = stream.toString
      stream.clear()
      result
    }

    def thisFile: String =
      new Throwable().getStackTrace().head.getFileName

    def thisDir: String = {
      val file = thisFile
      val i = file.lastIndexOf('/')
      if (i < 0)
        "" // this file is in root, default relative pathing works
      else
        file.substring(0, i + 1) // ensures that it ends with '/'
    }

    def fromThisDir(path: String): String = s"$thisDir$path"

    def readFileFromRoot(path: String): String =
      scala.io.Source.fromFile(path).getLines.mkString("\n")

    def readFileFromHere(path: String): String =
      readFileFromRoot(fromThisDir(path))
  }

  trait Trial extends Experiment {
    override def verify = true
  }

  trait SyntaxExperiment extends Experiment with Syntax {
    def normalize(x: Operator, s: String) =
      s"${x.parse(s).get.unparse}\n"
  }

  trait ModulesExperiment extends SyntaxExperiment with Modules

  object ProtoASTExperiment extends Experiment with ProtoAST {
    def leftParens  = Set("(")
    def rightParens = Set(")")

    val trees = List(
      "a () (b c (d) ((((e f))) g) (((h))))",
      "((((()))))",
      "()(()())((()())(()()))",
      "((((())))((",
      "(hi hi (hi hi (hi) hi) hi))(hi)")

    case object TopLevel extends UnclassifiedTag

    def run: String = {
      trees foreach { tree =>
        try {
          val t = ⊹(TopLevel, ProtoAST(tokenize(tree)): _*)
          puts(s"${t.print}\n")
        }
        catch {
          case p: Problem =>
            puts(s"${p.getMessage}")
        }
      }
      dump()
    }

    override def expected =
      """|TopLevel
         |  ∙(TokenAST, 0:a)
         |  ProtoAST
         |  ProtoAST
         |    ∙(TokenAST, 6:b)
         |    ∙(TokenAST, 8:c)
         |    ∙(TokenAST, 11:d)
         |    ProtoAST
         |      ProtoAST
         |        ∙(TokenAST, 18:e)
         |        ∙(TokenAST, 20:f)
         |      ∙(TokenAST, 25:g)
         |    ∙(TokenAST, 31:h)
         |
         |TopLevel
         |  ProtoAST
         |
         |TopLevel
         |  ProtoAST
         |  ProtoAST
         |    ProtoAST
         |    ProtoAST
         |  ProtoAST
         |    ProtoAST
         |      ProtoAST
         |      ProtoAST
         |    ProtoAST
         |      ProtoAST
         |      ProtoAST
         |
         |
         |((((())))((
         |          ^
         |expect right parenthesis after this
         |
         |
         |(hi hi (hi hi (hi) hi) hi))(hi)
         |                          ^
         |unmatched right parenthesis
         |
         |""".stripMargin
  }

  object SelfReferenceExperiment extends Experiment with Syntax {
    def run: String = {
      puts(TypeApplication.lhs.toList)
      puts(Application.opGenus)
      puts(Instantiation.opGenus)
      dump
    }
    override def expected =
      """|List(TypeApplication, ParenthesizedType, FreeTypeVar)
         |BinaryOpGenus(Term,Term,Term)
         |BinaryOpGenus(Term,Type,Term)
         |""".stripMargin
  }

  object ApplicationExperiment extends SyntaxExperiment {
    def run: String = {
      val s = "a (b (c d) e) f"
      puts(TypeApplication.parse(s).get.print)
      puts(Application.parse(s).get.print)
      dump
    }

    override def expected =
      """|TypeApplication
         |  TypeApplication
         |    ∙(FreeTypeVar, a)
         |    TypeApplication
         |      TypeApplication
         |        ∙(FreeTypeVar, b)
         |        TypeApplication
         |          ∙(FreeTypeVar, c)
         |          ∙(FreeTypeVar, d)
         |      ∙(FreeTypeVar, e)
         |  ∙(FreeTypeVar, f)
         |Application
         |  Application
         |    ∙(FreeVar, a)
         |    Application
         |      Application
         |        ∙(FreeVar, b)
         |        Application
         |          ∙(FreeVar, c)
         |          ∙(FreeVar, d)
         |      ∙(FreeVar, e)
         |  ∙(FreeVar, f)
         |""".stripMargin
  }

  object FunctionArrowExperiment extends SyntaxExperiment {
    val unicode = "(a → b) → (c → d)"
    val ascii   = "(a -> b) -> (c -> d)"

    override
    def expected = normalize(FunctionArrow, ascii  )
    def run = normalize(FunctionArrow, unicode)
  }

  object AscriptionExperiment extends SyntaxExperiment {
    val s = "x : σ0 → σ1 : τ"
    def run = {
      puts((Ascription parse s).get.print)
      dump
    }

    override def expected =
      """|Ascription
         |  Ascription
         |    ∙(FreeVar, x)
         |    FunctionArrow
         |      ∙(FreeTypeVar, σ0)
         |      ∙(FreeTypeVar, σ1)
         |  ∙(FreeTypeVar, τ)
         |""".stripMargin
  }

  object AtomListExperiment extends SyntaxExperiment {
    val s = " a b c d e "
    def run = {
      puts(AtomList.parse(s).get.print)
      dump
    }
    override def expected = "∙(AtomList, List(a, b, c, d, e))\n"
  }

  object CollapsedBinderExperiment extends SyntaxExperiment {
    val s = """\all β. α -> \ex α. α -> β"""

    def run = {
      val t = Type.parse(s).get
      puts(t.unparse)
      puts(t.print)
      dump
    }

    override def expected =
      """|∀β. α → ∃α. α → β
         |Universal, binder of β
         |  ∙(LiteralTag(java.lang.String), β)
         |  Annotation
         |    ∙(Nope, ())
         |    ∙(Nope, ())
         |  FunctionArrow
         |    ∙(FreeTypeVar, α)
         |    Existential, binder of α
         |      ∙(LiteralTag(java.lang.String), α)
         |      Annotation
         |        ∙(Nope, ())
         |        ∙(Nope, ())
         |      FunctionArrow
         |        TypeVar, bound of α
         |        TypeVar, bound of β
         |""".stripMargin
  }

  object ShadowyExperiment extends SyntaxExperiment {
    val t =
      ⊹(Universal, §("α"), Annotation.none(),
      ⊹(Universal, §("α"), Annotation.none(),
      ⊹(Universal, §("α"), Annotation.none(),
      ⊹(Universal, §("α"), Annotation.none(),
      ⊹(Universal, §("α"), Annotation.none(),
      ₌(∙(TypeVar, 1), ₌(∙(TypeVar, 2), ∙(TypeVar, 3))))))))

    def run = { puts(t.unparse) ; dump }
    override def expected = "∀α α₂ α₁ α₀ α. α₀ (α₁ α₂)\n"
  }

  trait Decomposition extends SyntaxExperiment {
    def decompose(s: String): String = {
      val (t, toks) = Term.parse(ProtoAST(s)).get
      t.blindPreorder.toSeq.zip(toks).foreach {
        case ((tf, _), tok) =>
          puts(Problem(tok, tf.tag.toString, 1).getMessage)
      }
      dump
    }
  }

  object SourceLocationExperiment extends Decomposition {
    val s =
      "Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x"

    def run = decompose(s)

    override def expected =
      """|
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         | ^
         |TypeAbstraction
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         | ^
         |FreeTypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |    ^
         |AnnotatedAbstraction
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |     ^
         |FreeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |          ^
         |Universal
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |          ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |          ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |          ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |          ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |            ^
         |Universal
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |            ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |            ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |            ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |            ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |               ^
         |TypeApplication
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |               ^
         |FreeTypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                  ^
         |Existential
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                   ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                       ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                       ^
         |Yeah
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                       ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                       ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                          ^
         |Existential
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                           ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                               ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                               ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                               ^
         |Yeah
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                   ^
         |Existential
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                    ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                        ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                        ^
         |Yeah
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                        ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                          ^
         |Yeah
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                           ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                              ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                  ^
         |Existential
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                   ^
         |LiteralTag(java.lang.String)
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                       ^
         |Annotation
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                       ^
         |Nope
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                       ^
         |Yeah
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                        ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                            ^
         |TypeVar
         |
         |
         |Λγ. λx : ∀α β. F (∃ε = α. ∃η = {}. ∃ζ = η {ε, β}. ∃ξ = {ζ}. ξ). x
         |                                                                ^
         |FreeVar
         |
         |""".stripMargin
  }

  object AbstractionsExperiment extends SyntaxExperiment {
    val s = "Λα β. λx : α → β . x"

    def run = {
      val t = Term.parse(s).get
      puts(t.unparse)
      val u = t(æ("ℤ"))(æ("ℚ"))
      puts(u.unparse)
      val v = u(χ("42"))
      puts(v.unparse)
      dump
    }

    override def expected =
      """|Λα β. λx : α → β. x
         |λx : ℤ → ℚ. x
         |42
         |""".stripMargin
  }

  object CStyleConditionalExperiment extends SyntaxExperiment with Trial {
    val s = "a ? b : c ? d : e"

    def run = s"${Term.parse(s).get.print}\n"
  }

  object DeclarationsExperiment extends ModulesExperiment {
    val either = "type Either α β = ∀γ. (α → γ) → (β → γ) → γ"

    val recListBody = "either Unit (α → List α → List α)"
    val recList = s"type List α = $recListBody"

    val id = "id = λx : α. x"
    val fix = "fix = λf : α → α. f (fix f)"

    val auto = "auto : (∀α. α → α) → (∀α. α → α)"

    def expectProblem(x: Operator, s: String): Unit =
      try { x.parse(s) }
      catch { case p: Problem => puts(p.getMessage) }

    def expectSuccess(op: Definitional, s: String): Unit =
      op.unapply(op.parse(s).get).get match {
        case (x, body) => puts(op.unparse(x, body))
      }

    def run = {
      expectSuccess(TypeSynonym, either)
      expectProblem(TypeSynonym, recList)
      expectSuccess(Definition, id)
      expectProblem(Definition, fix)
      expectSuccess(Signature, auto)
      dump
    }

    override def expected =
      """|type Either = ∀α β γ. (α → γ) → (β → γ) → γ
         |
         |type List α = either Unit (α → List α → List α)
         |     ^
         |recursive type synonym
         |
         |id = λx : α. x
         |
         |fix = λf : α → α. f (fix f)
         |    ^
         |recursive definition
         |
         |auto : (∀α. α → α) → ∀α. α → α
         |""".stripMargin
  }

  object FileParsingExperiment extends ModulesExperiment with Trial {
    val nats = fromThisDir("../examples/nat.ef")

    def run = try {
      val module = Module.fromFile(nats)
      puts(module.unparse)
      dump
    } catch {
      case e: java.io.FileNotFoundException =>
        // we're not in the source repo, giving up
        e.getMessage
    }

    // expectation does nothing,
    // but if this experiment is put on maintenance list,
    // we will catch exceptions.
  }

  object AlphaEquivExperiment extends SyntaxExperiment {
    val s = "∀α β. β → β. α → α"
    val t = "∀γ δ. δ → δ. γ → γ"

    def run = {
      val (σ, τ) = (Type.parse(s).get, Type.parse(t).get)
      puts(σ α_equiv τ)
      dump
    }

    override def expected = "true\n"
  }

  object AnnotatedBinderExperiment extends SyntaxExperiment {
    val t = λ("f", Type("α → β"), λ("x", Type("α"), Term("f x")))
    def run = {
      puts(s"t = ${t.unparse}")
      t match {
        case λ(f, α → β, λ(x, α0, f0 ₋ x0)) =>
          puts(s"t deconstructed to " +
            s"λ($f, ${α.unparse} → ${β.unparse}, " +
            s"λ($x, ${α0.unparse}, ${f0.unparse} ${x0.unparse}))")
      }
      dump
    }

    override def expected =
      """|t = λf : α → β. λx : α. f x
         |t deconstructed to λ(f, α → β, λ(x, α, f x))
         |""".stripMargin
  }

  object TypeListExperiment extends SyntaxExperiment {
    def test(s: String): Unit =
      puts(TypeList.parse(s).get.as[Seq[Tree]].map(_.unparse).toString)

    val lines =
      """|{}
         |{α → β, ∀γ. γ, List β}
         |""".stripMargin

    def run = {
      lines.lines.foreach { line => test(line) }
      dump
    }

    override def expected =
      """|List()
         |List(α → β, ∀γ. γ, List β)
         |""".stripMargin
  }

  object PrenexExperiment extends Experiment with Prenex {
    val types =
      """|(α → β) → (β → α)
         |((∀α. α → α) → (∀α. α → α)) → ((∀α. α → α) → (∀α. α → α))
         |""".stripMargin

    def run = {
      types.lines.foreach { line =>
        val τ = Type(line)
        puts(τ.unparse)
        puts(Prenex(τ).toType.unparse)
        puts()
      }
      dump
    }

    override def expected =
      """|(α → β) → β → α
         |(α → β) → β → α
         |
         |((∀α. α → α) → ∀α. α → α) → (∀α. α → α) → ∀α. α → α
         |∀α₂. ∃α₁ α₀. ∀α. ((α₂ → α₂) → α₁ → α₁) → (α₀ → α₀) → α → α
         |
         |""".stripMargin
  }

  object UnificationExperiment extends Experiment with Unification {
    val types = List[(String, String)](
      "α → β" -> "γ → δ",
      "α → α" -> "(β → β) → (γ → γ)"
    )

    def run = {
      types.foreach {
        case (type1, type2) =>
          val (σ, τ) = (Type(type1), Type(type2))
          val mgs = unifyMonotypesBy(_.head.toInt,
            σ.freeNames ++ τ.freeNames, σ, τ).get
          val μ = σ subst mgs
          val ν = τ subst mgs
          Seq(σ, τ, μ, ν).map(_.unparse).map(puts)
          puts()
      }
      dump
    }

    override def expected =
      """|α → β
         |γ → δ
         |γ → δ
         |γ → δ
         |
         |α → α
         |(β → β) → γ → γ
         |(γ → γ) → γ → γ
         |(γ → γ) → γ → γ
         |
         |""".stripMargin
  }

  // important scoping exercise
  // assumed during capturing of family heads
  object ScopingExperiment extends Experiment with ExistentialF {
    def run = {
      val β = "β"
      val γ = "γ"
      val τ =
        ∀(γ, Annotation.none(),
          ∀(β, Annotation.none(),
            ∀(β, Annotation(Some(β), Some(Seq(æ(γ)))), æ(β))))
      puts(τ.unparse)
      puts(τ.print)
      dump
    }

    override def expected =
      """|∀γ β₀. ∀β = β₀ {γ}. β
         |Universal, binder of γ
         |  ∙(LiteralTag(java.lang.String), γ)
         |  Annotation
         |    ∙(Nope, ())
         |    ∙(Nope, ())
         |  Universal, binder of β₀
         |    ∙(LiteralTag(java.lang.String), β)
         |    Annotation
         |      ∙(Nope, ())
         |      ∙(Nope, ())
         |    Universal, binder of β
         |      ∙(LiteralTag(java.lang.String), β)
         |      Annotation
         |        Yeah
         |          TypeVar, bound of β₀
         |        Yeah
         |          TypeVar, bound of γ
         |      TypeVar, bound of β
         |""".stripMargin
  }

  object AnnotationExperiment extends SyntaxExperiment {
    val s = "∀α = {}. ∀δ ε. ∃η ζ. ∃β = α {δ, ε, η, ζ}. ∀γ = β. γ"

    def run = {
      val τ = Type(s)
      puts(τ.unparse)
      dump
    }

    override def expected = s + "\n"
  }

  object NondeterminismExperiment extends Experiment with Nondeterminism {
    def run = {
      var i = 0
      val tape = Nondeterministic.tape
      while (tape.hasNext) {
        tape.next
        i += 1
        (1 to 5) foreach { _ => tape.read }
      }
      puts(i)
      dump
    }

    override def expected = "32\n"
  }

  object CaptureExperiment extends Experiment with ExistentialF {
    val types = List[(String, String)](
      ("∀α. α → α → ⊥", id()),
      // . rant 1: better not to capture
      ("∀α. α → (α → α → α)", id()),
      // . rant 2: better to capture
      ("∀α. α → (α → ⊥) → α", id()),
      // . rant 3: that is the question indeed!
      ("∀α. α → (α → α) → α", id()))

    def id(β: String = "β") = s"∀$β. $β → $β"

    def normalize(τ: Tree): Tree = Prenex(τ).normalize

    def run = {
      types.foreach {
        case (operator, operand) =>
          val fun = Type(operator)
          val arg = Type(operand)
          val rt0 = normalize(resultTypeCaptureNone(fun, arg).get)
          val rt1 = normalize(resultTypeCaptureAll (fun, arg).get)
          puts(s"     f : ${fun.unparse}")
          puts(s"     x : ${arg.unparse}")
          puts(s"(f x)₀ : ${rt0.unparse}")
          puts(s"(f x)₁ : ${rt1.unparse}")
          puts()
      }
      dump
    }

    override def expected =
      """|     f : ∀α. α → α → ⊥
         |     x : ∀β. β → β
         |(f x)₀ : ∀β. (β → β) → ⊥
         |(f x)₁ : ∃β. (β → β) → ⊥
         |
         |     f : ∀α. α → α → α → α
         |     x : ∀β. β → β
         |(f x)₀ : ∀β. (β → β) → (β → β) → β → β
         |(f x)₁ : ∃β₁ β₀. ∀β. (β₁ → β₁) → (β₀ → β₀) → β → β
         |
         |     f : ∀α. α → (α → ⊥) → α
         |     x : ∀β. β → β
         |(f x)₀ : ∀β. ((β → β) → ⊥) → β → β
         |(f x)₁ : ∀β₀ β. ((β₀ → β₀) → ⊥) → β → β
         |
         |     f : ∀α. α → (α → α) → α
         |     x : ∀β. β → β
         |(f x)₀ : ∀β. ((β → β) → β → β) → β → β
         |(f x)₁ : ∀β₁. ∃β₀. ∀β. ((β₁ → β₁) → β₀ → β₀) → β → β
         |
         |""".stripMargin
  }

  object EFStringExperiment extends Experiment with ExistentialF {
    val modules = List[String](
      s"""|n : $ℤ
          |n = 5
          |t : $Bool
          |t = false
          |""".stripMargin,
      "type X α = α → Y"
    )

    def run = {
      modules.zipWithIndex.foreach { case (source, i) =>
        Module(source).typeErrorInDefinitions match {
          case None =>
            puts(s"module #$i is type correct.\n")
          case Some(problem) =>
            puts(s"module #$i has type errors.\n" + problem.getMessage)
        }
      }
      dump
    }

    override def expected =
      """|module #0 is type correct.
         |
         |module #1 has type errors.
         |
         |type X α = α → Y
         |               ^
         |unknown type Y
         |
         |""".stripMargin
  }

  object DesugarExperiment extends Trial with Decomposition {
    val sugared   = "cond ? then : else"

    def run = decompose(sugared)
  }

  // UNFINISHED EXPERIMENT
  // objective: try to drop mandatory ascription in nats.ef
  object MatchNatExperiment extends Trial with ExistentialF {
    val nat = Type("∀ν. ν → (ν → ν) → ν")
    val nil = Type("∀β α. α → β → α")
    val mat = Type("∀φ. φ → ((∀ψ. ψ → (ψ → ψ) → ψ) → φ) → φ")

    val n2n = Type("∀β. (∀α. α → β → α) → ∀α. α → β → α")
    val m2m = →(mat, mat)

    // variants of applying nat to nil
    def variants = {
      val tape = Nondeterministic.tape
      while(tape.hasNext) {
        tape.next
        puts(resultType(nat, nil, tape).get.unparse)
      }
      dump
    }

    def run = {
      val t = ∀("α", "β")(→(æ("α"), æ("β")))
      puts(t.unparse)

      //puts("nil to mat: " + mayAscribe(nil, mat))
      //puts("n2n to m2m: " + mayAscribe(n2n, m2m))
      dump
    }
  }

  trait SootExperiment extends Experiment with SecondOrderOrderlessTypes

  object OrderlessExperiment extends SootExperiment {
    val s =
      s"""|five : ℤ
          |five = 5
          |
          |2+2=5 : ℤ
          |2+2=5 = true
          |
          |id : ∀ι. ι → ι
          |id = λx : α. x
          |
          |absurd-number : ℤ
          |absurd-number = ???
          |""".stripMargin

    def run = {
      val module = Module(s)
      val typing = new OrderlessTyping(module)
      module.dfn.foreach {
        case (x, t) =>
          val τ = module.sig(x)
          puts(s"${t.unparse} : ${τ.unparse}")
          typing.ascriptionError(typing.gatherConstraints(t), τ) match {
            case None =>
              puts("is fine\n")
            case Some(contradiction) =>
              puts(contradiction.msg)
          }
      }
      dump
    }

    override def expected =
      s"""|5 : ℤ
          |is fine
          |
          |true : ℤ
          |irreconciled constraint:
          |  β → β → β ⊑ ℤ
          |
          |λx : α. x : ∀ι. ι → ι
          |is fine
          |
          |??? : ℤ
          |is fine
          |
          |""".stripMargin
  }

  object TypeApplicationExperiment
      extends Experiment with Aliasing with IntsAndBools {
    val s =
      """|type Pair α β = ∀γ. (α → β → γ) → γ
         |""".stripMargin

    val src = "∀δ ε. Pair δ ε"
    val t = Type(src)

    def run = {
      val mod = Module(s)
      val syn = new SynonymResolution(mod)
      import syn._
      val τ = resolve(t)
      puts(s"$src = ${τ.unparse}")
      dump
    }

    override def expected =
      "∀δ ε. Pair δ ε = ∀δ ε γ. (δ → ε → γ) → γ\n"
  }

  object AbsLocationExperiment extends Decomposition with Trial {
    def s = "λm : ℤ. m"

    def run = decompose(s)
  }

  object DepthFirstSearchExperiment extends Experiment with Nondeterminism {
    // transform a list of reads/skips into a list of results
    def transform(spec: String): String = {
      val tape = DepthFirstSearch.tape
      val reads = spec.foldLeft[List[Char]](Nil) {
        case (reads, c) => c match {
          case '0' =>
            (if (tape.read == tape.ONE) '1' else '0') :: reads
          case '1' =>
            tape.next ; reads
          case c if '2' <= c && c <= '9' =>
            tape.readInt(c - '0').toString.head :: reads
          case _ =>
            reads
        }
      }
      reads.reverse.mkString
    }

    def test(s: String): Unit = try {
      puts(transform(s))
    } catch {
      case CarryBitSet => puts("carry")
    }

    def run = {
      test("0000 0000")
      test("1")
      test("010")
      test("0001 0001 0001 0001 0001 0001 0001 000")
      test("0001 001 00001 00000")
      test("0001 001 001 001")
      test("0001 001 001 001 001")
      test("0001 001 001 001 0001 000")
      test("51 51 51 51 5")
      test("21 21")
      dump
    }

    override def expected =
      """|00000000
         |carry
         |01
         |000001010011100101110111
         |00000010001010
         |000000110
         |carry
         |000000110110111
         |01234
         |carry
         |""".stripMargin
  }
}
