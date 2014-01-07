trait Gamma extends Syntax {
  gammaTrait =>

  private val ℤ = "ℤ"
  private val Bool = "Bool"

  final val intsAndBools = {
    val int        = æ(ℤ)
    val bool       = æ(Bool)
    val intLiteral = """(-)?\d+"""
    val intBinOp   = Type(s"$ℤ → $ℤ → $ℤ")
    val absurdity  = Type("∀a̧. a̧")
    val result: PartialFunction[String, Tree] = {
      case "+" | "-" | "*" | "/" | "%" =>
        intBinOp
      case "true" | "false" =>
        bool
      case "???" =>
        absurdity
      case n if n matches intLiteral =>
        int
    }
    result
  }

  def globalTypes: Set[String] = Set(ℤ, Bool)

  object DummyTokenTracker extends TokenTracker(Nil) {
    final override val next: Token =
      Token("", 0, Paragraph("#DUMMY", 0, ""))

    override def toString = "DummyTokenTracker"
  }

  case class TokenTracker(var tokens: Seq[Token]) {
    def next: Token = {
      val tok = tokens.head
      tokens = tokens.tail
      tok
    }
  }

  trait Γ {
    def prefix: BinderPrefix
    def vars: Map[String, Tree]

    def global: PartialFunction[String, Tree] = intsAndBools

    final val globalTypes: Set[String] = gammaTrait.globalTypes

    /* what type should "infer" be? different type systems
       may prefer different results. design it later. for
       now, this is an archive of what typing a conditional
       may look like.

    // intersection type
    def intersect(lhs: Tree, rhs: Tree): Status[Tree]
    // greater generality
    def canBe(moreGeneral: Tree, lessGeneral: Tree): Boolean

    def infer(t: Tree, toks: Seq[Token]): Tree =
      infer(t, toks.head, TokenTracker(toks.tail))

    def infer(t: Tree, tok: Token, toks: TokenTracker): Tree = t match {
      case ⊹(CStyleConditional, condition, thenBranch, elseBranch) =>
        val condType = infer(condition, toks.next, toks)
        val thenType = infer(thenBranch, toks.next, toks)
        val elseType = infer(elseBranch, toks.next, toks)
        if (! canBe(condType, æ(Bool)))
          throw Problem(tok,
            "expect Bool in condition, got ${condType.unparse}")
        intersect(thenType, elseType) match {
          case Success(resultType) =>
            resultType
          case Failure(msg) =>
            throw Problem(tok,
              s"""|cannot unify types of then-branch and else-branch.
                  |then-branch : ${thenType.unparse}
                  |else-branch : ${elseType.unparse}
                  |due to
                  |$msg
                  |""".stripMargin)
        }
      case _ =>
        throw Problem(tok, "don't know how to infer the type of ${t.tag}")
    }
     */
  }
}

trait GammaMLF extends Gamma with MLF {
  import BinderSpecSugar._

  // assume all synonyms have been resolved
  case class Γ_MLF(prefix: BinderPrefix, vars: Map[String, Tree]) extends Γ {
    def ⊢ (t: Tree): Tree = {
      val (prefix, body) =
        infer(t, DummyTokenTracker.next, DummyTokenTracker)
      reattach(prefix, body)
    }

    // algorithm W^F, figure 9 of MLF paper
    // stilted interface to remind of the correct usage of TokenTracker
    def infer(t: Tree, tok: Token, toks: TokenTracker):
        (BinderPrefix, Tree) =
      t match {
        case χ(x) =>
          (prefix, vars.withDefault(global)(x))

        case λ(x, σ0, a) =>
          val σ = ensureMonotypeBody(σ0)
          val toQuantify = σ0.freeNames -- globalTypes -- prefix.keySet
          val q1 = prefix ++ toQuantify.map(_ ⊒ ⊥())
          val (q2, τ) = Γ_MLF(q1, vars.updated(x, σ)).
            infer(a, toks.next, toks)
          val toAvoid = σ0.freeNames ++ q2.keySet
          val β = Subscript.newName(s"β_$x", toAvoid)
          val (q3, q4) = upArrow(q2, prefix.keySet)
          (q3, reattach(q4, ∀⊒(β, τ, ensureMonotypeBody(→(σ, æ(β))))))

        case ₋(a, b) =>
          val (q1, σ_a) =            this.infer(a, toks.next, toks)
          val (q2, σ_b) = Γ_MLF(q1, vars).infer(b, toks.next, toks)

          val toAvoid = t.freeNames ++ q2.keySet
          val α_a = Subscript.newName("α_a" , toAvoid)
          val α_b = Subscript.newName("α_b" , toAvoid)
          val β   = Subscript.newName("β_ab", toAvoid)
          val q3 = unify(q2 ++ Seq(α_a ⊒ σ_a, α_b ⊒ σ_b, β ⊒ ⊥()),
                         æ(α_a), →(æ(α_b), æ(β))) match {
            case Success(prefix) => prefix
            case Failure(msg) =>
              throw Problem(tok,
                s"""|Type error in applicatiopn
                    |
                    |  ${t.unparse}
                    |
                    |with operator type
                    |
                    |  ${reattach(q1, σ_a).unparse}
                    |
                    |and operand type
                    |
                    |  ${reattach(q2, σ_b).unparse}
                    |
                    |due to:
                    |$msg
                    |""".stripMargin)
          }
          val (q4, q5) = upArrow(q3, prefix.keySet)
          (q4, reattach(q5, æ(β)))
      }
  }
}
