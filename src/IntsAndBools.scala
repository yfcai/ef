trait IntsAndBools extends Aliasing {
  val ℤ = "ℤ"
  val Bool = "Bool"
  val ℤ_ascii = "Int"

  val realIntType =
    æ(if (I_hate_unicode)
      ℤ_ascii
    else
      ℤ)

  // don't worry about opchars. they're dispensible.
  val realBoolType =
    if (I_hate_unicode)
      Type("∀beta. beta → beta → beta")
    else
      Type("∀β. β → β → β")

  val globalTypes: Map[String, Tree] = Map(
    ℤ -> realIntType,
    ℤ_ascii -> realIntType,
    Bool -> realBoolType)

  def globalTerms: PartialFunction[String, Tree] = primitiveType

  def primitiveType: PartialFunction[String, Tree] = {
    val int        = globalTypes(ℤ)
    val bool       = globalTypes(Bool)
    val intLiteral = """(-)?\d+"""
    val intBinOp   = Type(s"$ℤ → $ℤ → $ℤ")
    val intComp    = Type(s"$ℤ → $ℤ → (${bool.unparse})")
    val iterate    =
      if (I_hate_unicode)
        Type(s"ℤ → ∀a. a → (ℤ → a → a) → a")
      else
        Type(s"ℤ → ∀α. α → (ℤ → α → α) → α")
    val absurdity  =
      if (I_hate_unicode)
        Type("∀absurd. absurd")
      else
        Type("∀a̧. a̧")
    val result: PartialFunction[String, Tree] = {
      case "+" | "-" | "*" | "/" | "%" =>
        intBinOp
      case "≡" | "≤" | "≥" | "==" | "<" | ">" | "<=" | ">=" =>
        intComp
      case "true" | "false" =>
        bool
      case "iterate" =>
        iterate
      case "???" =>
        absurdity
      case n if n matches intLiteral =>
        int
    }
    result
  }

  // context with infinite & finite part
  case class Gamma(
    finite: Map[String, Tree],
    infinite: PartialFunction[String, Tree]) {

    def contains(x: String): Boolean =
      finite.contains(x) || infinite.isDefinedAt(x)

    def updated(x: String, τ: Tree): Gamma =
      Gamma(finite.updated(x, τ), infinite)

    def apply(x: String): Tree =
      finite.withDefault(infinite)(x)

    def ++(_finite: Map[String, Tree]): Gamma =
      Gamma(finite ++ _finite, infinite)
  }

  val Γ0 = Gamma(Map.empty, primitiveType)
}
