/** Examples of system F from Pierce's Types and Programming Languages */
trait SystemFExamples extends SystemF {
  import SystemF._

  def buildMap[N <% Name, T <% Type](seq: (N, T)*): Map[Name, Type] =
    seq.map({ case (k, v) => (k: Name, v: Type) })(collection.breakOut)

  def list(τ : Type): Type = ★("List", τ)

  /** Church-encoding of Booleans is practical and convenient. */
  val bool: Type = ∀("α")("α" →: "α" →: "α")

  val primitives: Map[Name, Type] = buildMap(
    "undefined" -> ∀("α")("α"),
    "fix"   -> ∀("α")(("α" →: "α") →: ("α" →: "α")),
    "succ"  -> "ℕ" →: "ℕ",
    "nil"   -> ∀("α")(list("α")),
    "cons"  -> ∀("α")("α" →: list("α") →: list("α")),
    "isnil" -> ∀("α")(list("α") →: bool),
    "head"  -> ∀("α")(list("α") →: "α"),
    "tail"  -> ∀("α")(list("α") →: list("α"))
  )

  /** An example of implementing primitives and literals by an infinite
    * global environment
    */
  val Γ0: PartialFunction[Name, Type] = primitives.orElse[Name, Type] {
    // natural literals
    case StringLiteral(s) if s matches """\d+""" =>
      α("ℕ")
  }

  private[this]
  def fTerm[T <% Type](desc: String, canon: Term, localTypes: (String, T)*):
      (String, FTerm) =
    fTerm(desc, canon, localTypes.to_Γ)

  private[this]
  def fTerm(desc: String, canon: Term,
            localTypes: PartialFunction[Name, Type]): (String, FTerm) =
    (desc, FTerm(canon, localTypes orElse Γ0, Map.empty[Name, Name]))

  private[this]
  implicit class SequenceToContext[T <% Type](seq: Seq[(String, T)]) {
    def to_Γ : Map[Name, Type] =
      seq.map({
        case (s, τ) => (StringLiteral(s), τ : Type)
      })(collection.breakOut)
  }

  private[this]
  implicit class ExtendPartialFunction
    (f: PartialFunction[Name, Type])
  {
    def extend(g: PartialFunction[Name, Type]):
        PartialFunction[Name, Type] = g orElse f

    def extend[T <% Type](seq: (String, T)*):
        PartialFunction[Name, Type] = extend(seq.to_Γ)
  }

  val id = fTerm("id", Λ("α", λ("x")("x")), "x" -> "α")

  val idNat = fTerm("idNat", id._2.canon □ "ℕ", "x" -> "α")

  val double = fTerm("double",
    Λ("α", λ("f", "a")("f" ₋ ("f" ₋ "a"))),
    "f" -> "α" →: "α",
    "a" -> α("α")
  )

  val doubleTerm    = double._2.canon
  val doubleContext = double._2.Γ

  val doubleNat = fTerm("doubleNat", doubleTerm □ "ℕ", doubleContext)

  val doubleNatArrowNat = fTerm(
    "doubleNatArrowNat",
    doubleTerm □ ("ℕ" →: "ℕ"), doubleContext
  )

  val quadrupleSucc3 = fTerm(
    "quadrupleSucc3",
    doubleNat._2.canon ₋ λ("x")("succ" ₋ ("succ" ₋ "x")) ₋ "3",
    doubleContext.extend("x" -> "ℕ")
  )

  val selfApp = fTerm(
    "selfApp",
    λ("x")("x" □ (id._2.getType) ₋ "x"),
    "x" -> id._2.getType
  )

  val quadruple = fTerm(
    "quadruple",
    Λ("α", doubleTerm □ ("α" →: "α") ₋ (doubleTerm □ "α")),
    doubleContext
  )

  val map = fTerm(
    "map",
    Λ("α", Λ("β",
      λ("f") {
        "fix" □ (list("α") →: list("β")) ₋ λ("m", "l") {
          "isnil" □ α("α") ₋ "l" □ list("β") ₋ (
            "nil" □ α("β")
          ) ₋ (
            "cons" □ α("β") ₋ ("f" ₋ ("head" □ α("α") ₋ "l")) ₋
                              ("m" ₋ ("tail" □ α("α") ₋ "l"))
          )
        }
      }
    )),
    "f" -> "α" →: "β",
    "m" -> list("α") →: list("β"),
    "l" -> list("α")
  )

  val listOfSystemFExamples = List(
    id, idNat, double, doubleNat, doubleNatArrowNat,
    quadrupleSucc3, selfApp, quadruple, map
  )
}

object TestF extends SystemFExamples with PrettyF with MinimalQuantification {
  def main(args: Array[String]) {
    primitives foreach (_._2.ensureMinimalQuantification)

    listOfSystemFExamples foreach {
      case (desc, t) =>
        println(s"$desc : ${pretty(t.getType)}")
        println(s"$desc = ${pretty(t.getTerm)}\n")
    }
  }
}
