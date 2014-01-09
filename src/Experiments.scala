object Experiments {
  val debug = false

  val onTrial: Experiment =
    CaptureExperiment

  val experiments = List[Experiment](
    ScopingExperiment,
    PrefixExperiment,
    UnificationExperiment,
    TypeListExperiment,
    PrenexExperiment,
    AnnotatedBinderExperiment,
    AlphaEquivExperiment,
    CStyleConditionalExperiment,
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
    val s = "∀α = (∀α. α → α). List (∃β = α. β)"

    def run = {
      val t = (Type parse s).get
      puts(t.unparse)
      puts(t.print)
      dump
    }

    override def expected =
      """|∀α = (∀α. α → α). List (∃β = α. β)
         |UniversalBound, binder of α
         |  ∙(LiteralTag(java.lang.String), α)
         |  UniversalQuantification, binder of α
         |    ∙(LiteralTag(java.lang.String), α)
         |    FunctionArrow
         |      TypeVar, bound of α
         |      TypeVar, bound of α
         |  TypeApplication
         |    ∙(FreeTypeVar, List)
         |    ExistentialBound, binder of β
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
    val s = """∀α = ∀α. α → α. List (∃β = α. β)"""

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
         |∀α = ∀α. α → α. List (∃β = α. β)
         | ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |      ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |         ^
         |TypeVar
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |             ^
         |TypeVar
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |           ^
         |FunctionArrow
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |     ^
         |UniversalQuantification
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                ^
         |FreeTypeVar
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                       ^
         |LiteralTag(java.lang.String)
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                           ^
         |TypeVar
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                              ^
         |TypeVar
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                      ^
         |ExistentialBound
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |                ^
         |TypeApplication
         |
         |#LINE:1
         |∀α = ∀α. α → α. List (∃β = α. β)
         |^
         |UniversalBound
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

  object PrenexExperiment extends Experiment with Prenex {
    val types =
      """|(α → β) → (β → α)
         |((∀α. α → α) → (∀α. α → α)) → ((∀α. α → α) → (∀α. α → α))
         |(∀α = ((∃α = ((∀α. α) → ⊥). α → ⊥) → ⊥). α → ⊥) → ⊥
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
         |(∀α = ((∃α = ((∀α. α) → ⊥). α → ⊥) → ⊥). α → ⊥) → ⊥
         |∃α = (∀α = (∃α. α → ⊥). (α → ⊥) → ⊥). (α → ⊥) → ⊥
         |
         |""".stripMargin
  }

  object TypeListExperiment extends SyntaxExperiment {
    def test(s: String): Unit =
      puts(TypeList.parse(s).get.as[Seq[Tree]].map(_.unparse).toString)

    val lines =
      """|{}
         |{α → β, ∀γ. γ, List β}
         |""".stripMargin

    // this will never happen in practice.
    // in practice, an uncertain quantifier never occurs in body:
    //
    //   ∀γ. ∃δ. ∀α = {γ, δ}. ∃β = {}. ∀α₀ = α. ∀β₀ = β. α₀ → β₀
    //
    val τ = "∀α = {}. ∃β = {List γ, γ → δ}. α → β"

    def run = {
      lines.lines.foreach { line => test(line) }
      puts(Type(τ).print)
      dump
    }

    override def expected =
      """|List()
         |List(α → β, ∀γ. γ, List β)
         |UniversalUncertainty, binder of α
         |  ∙(LiteralTag(java.lang.String), α)
         |  ∙(TypeList, List())
         |  ExistentialUncertainty, binder of β
         |    ∙(LiteralTag(java.lang.String), β)
         |    ∙(TypeList, """.stripMargin +
      "List(⊹(TypeApplication, ∙(FreeTypeVar, List), ∙(FreeTypeVar, γ))," +
      " ⊹(FunctionArrow, ∙(FreeTypeVar, γ), ∙(FreeTypeVar, δ))))\n" +
      """|    FunctionArrow
         |      TypeVar, bound of α
         |      TypeVar, bound of β
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
          val mgs = unifyMonotypes(σ.freeNames ++ τ.freeNames, σ, τ).get
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
         |α → β
         |α → β
         |
         |α → α
         |(β → β) → γ → γ
         |(β → β) → β → β
         |(β → β) → β → β
         |
         |""".stripMargin
  }

  object PrefixExperiment extends Experiment with ExistentialF {
    val t = "∀γ. ∃δ. ∀α = {γ, δ}. ∃β = {}. ∀α′ = α. ∀β′ = α. α′ → β′"

    def run = {
      val τ = Prenex(Type(t))
      puts(τ.toType.unparse)
      val prefix = Prefix(τ.prefix)
      puts(s"∀  = ${prefix.universal}")
      puts(s"∀? = ${prefix.universalParent}")
      puts(s"∀= = ${prefix.universalChild}")
      puts(s"∃  = ${prefix.existential}")
      puts(s"∃? = ${prefix.existentialParent}")
      puts(s"∃= = ${prefix.existentialChild}")
      puts(s"CP = ${prefix.parent}")
      puts(s"PC = ${prefix.children}")
      puts(s"DT = ${prefix.debts.map({
        case (k, v) => (k, v.map(_.unparse))
      })}")
      dump
    }

    override def expected =
      """|∀γ. ∃δ. ∀α = {γ, δ}. ∃β = {}. ∀α′ = α. ∀β′ = α. α′ → β′
         |∀  = Set(γ)
         |∀? = Set(α)
         |∀= = Set(α′, β′)
         |∃  = Set(δ)
         |∃? = Set(β)
         |∃= = Set()
         |CP = Map(α′ -> α, β′ -> α)
         |PC = Map(α -> Set(α′, β′), β -> Set())
         |DT = Map(α -> List(γ, δ), β -> List())
         |""".stripMargin
  }

  // important scoping exercise
  // assumed during capturing of family heads
  object ScopingExperiment extends Experiment with ExistentialF {
    def run = {
      val β = "β"
      val τ = ∀(β, ∀=(β, æ(β), æ(β)))
      puts(s"∀(β, ∀=(β, æ(β), æ(β))) = ${τ.unparse}")
      dump
    }

    override def expected =
      """|∀(β, ∀=(β, æ(β), æ(β))) = ∀β₀. ∀β = β₀. β
         |""".stripMargin
  }

  object CaptureExperiment extends Experiment with ExistentialF {
    val choose = Type("∀α. α → α → α")
    val absurd = Type("∀ω. ω")
    val id = Type("∀ι. ι → ι")

    def run = {
      val abs = Prenex(resultType(choose, absurd).get).toType
      puts(abs.unparse)
      val cid = Prenex(resultType(choose, id).get).toType
      puts(cid.unparse)
      dump
    }
  }
}
