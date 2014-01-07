object Experiments {
  val debug = false

  val onTrial: Experiment =
    AnnotatedBinderExperiment

  val experiments = List[Experiment](
    AnnotatedBinderExperiment,
    AlphaEquivExperiment,
    CStyleConditionalExperiment,
    MLFExperiment,
    FileParsingExperiment,
    DeclarationsExperiment,
    SourceLocationExperiment,
    CStyleConditionalExperiment,
    AbstractionsExperiment,
    BoundedQuantificationExperiment,
    ShadowyExperiment,
    CollapsedBinderExperiment,
    AtomListExperiment,
    AscriptionExperiment,
    FunctionArrowExperiment,
    ApplicationExperiment,
    SelfReferenceExperiment,
    ProtoASTExperiment).reverse

  def maintenance() = experiments foreach { ex =>
    if (ex.run != ex.expected) sys error s"failed: $ex"
  }

  def main(args: Array[String]) = {
    if (debug) onTrial.debug
    println("MAINTAINING ...")
    maintenance()
    println("MAINTENANCE SUCCESSFUL")
    if (! debug) onTrial.trial
  }

  trait Experiment {
    def run: String
    def expected: String = "UNEXPECTED"

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
  }

  trait SyntaxExperiment extends Experiment with Syntax {
    def normalize(x: Operator, s: String) =
      s"${x.parse(s).get.unparse}\n"
  }

  trait ModulesExperiment extends SyntaxExperiment with Modules

  object ProtoASTExperiment extends Experiment with ProtoAST {
    val keywords: Set[String] = Set("(", ")")
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
         |#LINE:1
         |((((())))((
         |          ^
         |expect right parenthesis after this
         |
         |#LINE:1
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
    def run      = normalize(FunctionArrow, unicode)
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
         |UniversalQuantification, binder of β
         |  ∙(LiteralTag(java.lang.String), β)
         |  FunctionArrow
         |    ∙(FreeTypeVar, α)
         |    ExistentialQuantification, binder of α
         |      ∙(LiteralTag(java.lang.String), α)
         |      FunctionArrow
         |        TypeVar, bound of α
         |        TypeVar, bound of β
         |""".stripMargin
  }

  object ShadowyExperiment extends SyntaxExperiment {
    val t =
      ⊹(UniversalQuantification, §("α"),
        ⊹(UniversalQuantification, §("α"),
          ⊹(UniversalQuantification, §("α"),
            ⊹(UniversalQuantification, §("α"),
              ⊹(UniversalQuantification, §("α"),
                ₌(∙(TypeVar, 1), ₌(∙(TypeVar, 2), ∙(TypeVar, 3))))))))

    def run = { puts(t.unparse) ; dump }
    override def expected = "∀α α₂ α₁ α₀ α. α₀ (α₁ α₂)\n"
  }

  object BoundedQuantificationExperiment extends SyntaxExperiment {
    val s = "∀α ⊒ (∀α. α → α). List (∃β ⊒ α. β)"

    def run = {
      val t = (Type parse s).get
      puts(t.unparse)
      puts(t.print)
      dump
    }

    override def expected =
      """|∀α ⊒ (∀α. α → α). List (∃β ⊒ α. β)
         |BoundedUniversal, binder of α
         |  ∙(LiteralTag(java.lang.String), α)
         |  UniversalQuantification, binder of α
         |    ∙(LiteralTag(java.lang.String), α)
         |    FunctionArrow
         |      TypeVar, bound of α
         |      TypeVar, bound of α
         |  TypeApplication
         |    ∙(FreeTypeVar, List)
         |    BoundedExistential, binder of β
         |      ∙(LiteralTag(java.lang.String), β)
         |      TypeVar, bound of α
         |      TypeVar, bound of β
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

  object CStyleConditionalExperiment extends SyntaxExperiment {
    val s = "a ? b : c ? d : e"

    def run = s"${Term.parse(s).get.print}\n"
    override def expected =
      """CStyleConditional
         |  ∙(FreeVar, a)
         |  ∙(FreeVar, b)
         |  CStyleConditional
         |    ∙(FreeVar, c)
         |    ∙(FreeVar, d)
         |    ∙(FreeVar, e)
         |""".stripMargin
  }

  object SourceLocationExperiment extends SyntaxExperiment {
    val s = """∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)"""

    def run = {
      val (t, toks) = Type.parse(ProtoAST(s)).get
      withTokens(t, toks).fold[Unit] {
        case (tf, tok) =>
          puts(Problem(tok, tf.tag.toString, 1).getMessage)
      }
      dump
    }

    override def expected =
      """|#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         | ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |      ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |         ^
         |TypeVar
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |             ^
         |TypeVar
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |           ^
         |FunctionArrow
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |     ^
         |UniversalQuantification
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                ^
         |FreeTypeVar
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                       ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                           ^
         |TypeVar
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                              ^
         |TypeVar
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                      ^
         |BoundedExistential
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |                ^
         |TypeApplication
         |
         |#LINE:1
         |∀α ⊒ ∀α. α → α. List (∃β ⊒ α. β)
         |^
         |BoundedUniversal
         |
         |""".stripMargin
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
         |#LINE:1
         |type List α = either Unit (α → List α → List α)
         |^
         |recursive type synonym
         |
         |id = λx : α. x
         |#LINE:1
         |fix = λf : α → α. f (fix f)
         |    ^
         |recursive definition
         |
         |auto : (∀α. α → α) → ∀α. α → α
         |""".stripMargin
  }

  object FileParsingExperiment extends ModulesExperiment {
    def thisFile = new Throwable().getStackTrace().head.getFileName
    val nats = thisFile.substring(0, thisFile.lastIndexOf('/') + 1) +
      "../examples/nats.ef"

    def run = {
      val module = Module.fromFile(nats)
      puts(module.unparse)
      dump
    }

    // expectation does nothing,
    // but if this experiment is put on maintenance list,
    // we will catch exceptions.
    override def expected = run
  }

  object MLFExperiment extends Experiment with MLF with Syntax {
    val syntax = this
    import BinderSpecSugar._

    def A(xs: String): BinderPrefix =
      Map(xs.map(_.toString ⊒ ⊥()): _*)

    val testCases = List[(BinderPrefix, String, String, String)](
      // ∀α β. α → β with ∀γ δ. γ → δ
      (A("αβγδ"), "α → β", "γ → δ", "α → β"),
      // choose id
      (A("αβ"), "α", "β → β", "α → α"),
      // choose id id
      (A("βγ") + ("α" ≡ "β → β"), "α", "γ → γ", "α"),
      // selfapp id
      (A("γ") + ("α" ≡ "∀β. β → β"), "α", "γ → γ", "α"),
      // revapp id
      (A("αβγ"), "α", "γ → γ", "(α → β) → β"),
      // revapp id poly
      (A("βγδ") + ("α" ≡ "γ → γ") + ("ε" ≡ "δ → δ"),
        "α → β", "ε → ℤ", "β")
    )

    def run = {
      testCases.foreach {
        case (prefix, left, right, target) =>
          val (lhs, rhs) = (Type.parse(left).get, Type.parse(right).get)
          val τ = Type.parse(target).get
          puts(s"unify ${lhs.unparse} and ${rhs.unparse}")
          puts(s"under prefix ${pretty(prefix).lines.mkString(", ")}")
          put (s"yields")
          puts(unify(prefix, lhs, rhs) match {
            case Failure(msg) =>
              s"\nFailure\n  $msg"
            case Success(mgp) =>
              s""" ${
                normalize(linearizePrefix(mgp), τ).unparse
              }\nSuccess\n${
                pretty(mgp).lines.map("  " + _).mkString("\n")}"""
          })
          puts()
      }
      dump
    }

    override def expected =
      """|unify α → β and γ → δ
         |under prefix ∀α ⊒ ⊥, ∀β ⊒ ⊥, ∀γ ⊒ ⊥, ∀δ ⊒ ⊥
         |yields ∀α β. α → β
         |Success
         |  ∀α ⊒ ⊥
         |  ∀β ⊒ ⊥
         |  ∀γ = α
         |  ∀δ = β
         |
         |unify α and β → β
         |under prefix ∀α ⊒ ⊥, ∀β ⊒ ⊥
         |yields ∀β. (β → β) → β → β
         |Success
         |  ∀β ⊒ ⊥
         |  ∀α = β → β
         |
         |unify α and γ → γ
         |under prefix ∀β ⊒ ⊥, ∀γ ⊒ ⊥, ∀α = β → β
         |yields ∀γ. γ → γ
         |Success
         |  ∀γ ⊒ ⊥
         |  ∀β = γ
         |  ∀α = β → β
         |
         |unify α and γ → γ
         |under prefix ∀α = ∀β. β → β, ∀γ ⊒ ⊥
         |yields ∀γ. γ → γ
         |Success
         |  ∀γ ⊒ ⊥
         |  ∀β = γ
         |  ∀α = β → β
         |
         |unify α and γ → γ
         |under prefix ∀α ⊒ ⊥, ∀β ⊒ ⊥, ∀γ ⊒ ⊥
         |yields ∀β γ. ((γ → γ) → β) → β
         |Success
         |  ∀β ⊒ ⊥
         |  ∀γ ⊒ ⊥
         |  ∀α = γ → γ
         |
         |unify α → β and ε → ℤ
         |under prefix ∀β ⊒ ⊥, ∀γ ⊒ ⊥, ∀δ ⊒ ⊥, ∀α = γ → γ, ∀ε = δ → δ
         |yields ℤ
         |Success
         |  ∀β = ℤ
         |  ∀γ ⊒ ⊥
         |  ∀α = γ → γ
         |  ∀δ = γ
         |  ∀ε = δ → δ
         |
         |""".stripMargin
  }

  object AlphaEquivExperiment extends SyntaxExperiment {
    val s = "∀α ⊒ ∀β. β → β. α → α"
    val t = "∀γ ⊒ ∀δ. δ → δ. γ → γ"

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

  // DEFUNCT
  object MonoBodyExperiment extends SyntaxExperiment with MLF {
    def test(s: String): Unit =
      puts(ensureMonotypeBody(Type(s)).unparse)

    val auto = "(∀α. α → α) → (∀β. β → β)"

    def run = {
      test(auto)
      test(s"∀γ = $auto. γ")
      dump
    }

    override def expected =
      """|∀α₀. ∀α = (α₀ → α₀). ∀β₀. ∀β = (β₀ → β₀). α → β
         |∀γ = (∀α₀. ∀α = (α₀ → α₀). ∀β₀. ∀β = (β₀ → β₀). α → β). γ
         |""".stripMargin
  }

  // DEFUNCT
  object GammaMLFExperiment extends Experiment with GammaMLF {
    val subjects = List[(String, String)](
      "five" -> "5",
      "single-id" -> "single id",
      "choose-5" -> "choose 5",
      "choose-id" -> "choose id",
      "choose-id-auto" -> "choose-id auto"
    )

    val badSubjects = List[(String, String)](
      "id" -> "λx : α. x",
      "auto" -> "λx : ∀ω. ω → ω. x x",
      "choose" -> "λx : χ. λy : χ. y",
      "choose-id-auto" -> "choose-id auto"
    )

    val postulates = Map[String, Tree](
      "single" -> Type("∀σ. σ → List σ"),
      "id" -> Type("∀α. α → α"),
      "auto" -> Type("∀ω = (∀β. β → β). ω → ω"),
      "choose" -> Type("∀χ. χ → χ → χ")
    )

    val ∅ : BinderPrefix = Map.empty

    override def globalTypes =
      super.globalTypes + "List"

    def run = {
      var vars = postulates
      subjects.foreach {
        case (x, xdef) =>
          val t = Term(xdef)
          val τ = Γ_MLF(∅, vars) ⊢ t
          vars = vars.updated(x, τ)
          puts(s"$x : ${τ.unparse}")
          puts(s"$x : ${normalize(τ).unparse}")
          puts(s"$x = ${t.unparse}\n")
      }
      dump
    }
  }
}
