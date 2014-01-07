trait Gamma extends Syntax {
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

  final val intAndBoolTypes = Set(ℤ, Bool)

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
    def globalTypes: Set[String] = intAndBoolTypes

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

    def canBe(moreGeneral: Tree, lessGeneral: Tree): Boolean = {
      val free = moreGeneral.freeNames ++ lessGeneral.freeNames
      val α = Subscript.newName("α", free)
      val β = Subscript.newName("β", free) // β can't collide with α
      val Q = unify(Map(α ⊒ moreGeneral, β ≡ lessGeneral), æ(α), æ(β))
      Q.toBoolean
    }

    def intersect(lhs: Tree, rhs: Tree): Status[Tree] = {
      val free = lhs.freeNames ++ rhs.freeNames
      val α = Subscript.newName("α", free)
      val β = Subscript.newName("β", free) // β can't collide with α
      val Q = unify(Map(α ⊒ lhs, β ⊒ rhs), æ(α), æ(β))
      Q.map(mgq => reattach(mgq, æ(α)))
    }

    // algorithm W^F
    // stilted interface to remind of the correct usage of TokenTracker
    def infer(t: Tree, tok: Token, toks: TokenTracker):
        (BinderPrefix, Tree) =
      t match {
        case χ(x) =>
          (prefix, vars(x))

        case λ(x, σ0, t) =>
          val σ = ensureMonotypeBody(σ0)
          val toQuantify = σ.freeNames -- globalTypes -- prefix.keySet
          val q1 = prefix ++ toQuantify.map(_ ⊒ ⊥())
          val (q2, τ) = Γ_MLF(q1, vars.updated(x, σ)).
            infer(t, toks.next, toks)

          ???

      }
  }
}
