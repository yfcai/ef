/** Examples of system F from Pierce's Types and Programming Languages */
trait SystemFExamples extends SystemF {
  import SystemF._

  /** An example of implementing primitives and literals by an infinite
    * global environment
    */
  val Γ0: PartialFunction[Name, Type] =
    Map(("succ": Name) -> "ℕ" →: "ℕ").orElse[Name, Type] {
      // natural literals
      case StringLiteral(s) if s matches """\d+""" =>
        α("ℕ")
    }

  private[this]
  def fTerm[T <% Type](canon: Term, localTypes: (String, T)*): FTerm =
    fTerm(canon, localTypes.to_Γ)

  private[this]
  def fTerm(canon: Term, localTypes: PartialFunction[Name, Type]): FTerm = {
    FTerm(canon, localTypes orElse Γ0, Map.empty[Name, Name])
  }

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

  val id = fTerm(Λ("α", λ("x")("x")), "x" -> "α")

  val idNat = fTerm(id.canon □ "ℕ", "x" -> "α")

  val double = fTerm(
    Λ("α", λ("f", "a")("f" ₋ ("f" ₋ "a"))),
    "f" -> "α" →: "α",
    "a" -> α("α")
  )

  val doubleNat = fTerm(double.canon □ "ℕ", double.Γ)

  val doubleNatArrowNat = fTerm(double.canon □ ("ℕ" →: "ℕ"), double.Γ)

  val quadrupleSucc3 = fTerm(
    doubleNat.canon ₋ λ("x")("succ" ₋ ("succ" ₋ "x")) ₋ "3",
    double.Γ.extend("x" -> "ℕ")
  )

  val selfApp = fTerm(
    λ("x")("x" □ (id.getType) ₋ "x"),
    "x" -> id.getType
  )

  val quadruple = fTerm(
    Λ("α", double.canon □ ("α" →: "α") ₋ (double.canon □ "α")),
    double.Γ
  )

  val listOfSystemFExamples = List(
    id, idNat, double, doubleNat, doubleNatArrowNat,
    quadrupleSucc3, selfApp, quadruple
  )
}

object TestF extends SystemFExamples with PrettyF {
  def main(args: Array[String]) {
    listOfSystemFExamples foreach {
      t => println(pretty(t))
    }
  }
}
