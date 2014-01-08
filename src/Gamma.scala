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
