trait IntsAndBools extends Aliasing {
  val ℤ = "ℤ"
  val Bool = "Bool"
  val ℤ_ascii = "Int"
  val globalTypes: Map[String, Tree] = Map(
    ℤ -> æ(ℤ),
    ℤ_ascii -> æ(ℤ),
    Bool -> Type("∀β. β → β → β"))

  def globalTerms: PartialFunction[String, Tree] = primitiveType

  def primitiveType: PartialFunction[String, Tree] = {
    val int        = globalTypes(ℤ)
    val bool       = globalTypes(Bool)
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
}
