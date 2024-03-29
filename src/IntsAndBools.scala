trait IntsAndBools extends Aliasing {
  val ℤ = "ℤ"
  val Bool = "Bool"
  val ℤ_ascii = "Int"

  def realIntType =
    æ(if (I_hate_unicode)
      ℤ_ascii
    else
      ℤ)

  // don't worry about opchars. they're dispensible.
  def realBoolType =
    if (I_hate_unicode)
      Type("∀beta. beta → beta → beta")
    else
      Type("∀β. β → β → β")

  def globalTypes: Map[String, Tree] = Map(
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
        Type(s"∀a. ℤ → a → (ℤ → a → a) → a")
      else
        Type(s"∀α. ℤ → α → (ℤ → α → α) → α")
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
    infinite: PartialFunction[String, Tree],
    types: Set[String]) {

    def contains(x: String): Boolean =
      finite.contains(x) || infinite.isDefinedAt(x)

    def updated(x: String, τ: Tree): Gamma =
      Gamma(finite.updated(x, τ), infinite, types)

    def apply(x: String): Tree =
      finite.withDefault(infinite)(x)

    def ++(_finite: Map[String, Tree]): Gamma =
      Gamma(finite ++ _finite, infinite, types)

    def addType(α: String): Gamma =
      Gamma(finite, infinite, types + α)

    def addTypes(moreTypes: Iterable[String]): Gamma =
      Gamma(finite, infinite, types ++ moreTypes)

    def hasType(α: String): Boolean = types(α)

    def badType(α: String): Boolean = ! hasType(α)

    def badTypes(someTypes: Set[String]): Set[String] =
      someTypes -- types
  }

  def Γ0 = Gamma(Map.empty, primitiveType, globalTypes.keySet)
}

trait PrimitiveLists extends IntsAndBools {
  override def globalTypes: Map[String, Tree] =
    super.globalTypes.updated("List", æ("List"))

  override def Γ0 = {
    val α = if (I_hate_unicode) "a" else "α"
    super.Γ0 ++ Map(
      "nil" -> Type(s"∀$α. List $α"),
      "cons" -> Type(s"∀$α. $α → List $α → List $α"),
      "isnil" -> Type(s"∀$α. List $α → Bool"),
      "head" -> Type(s"∀$α. List $α → $α"),
      "tail" -> Type(s"∀$α. List $α → List $α"))
  }
}
