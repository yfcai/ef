import scala.language.implicitConversions

trait SystemF extends TypedTerms with Substitution {
  object SystemF {
    case class Λ(alpha: Name, body: Term) extends Term
    case class □(term: Term, typeArg: Type) extends Term
  }

  implicit class typeApplicationForTerms[T <% Term](t: T) {
    def □ (τ : Type): Term = SystemF.□(t, τ)
  }

  case class FTerm(canon: Term,
                   Γ: PartialFunction[Name, Type],
                   names: Map[Name, Name])
  extends CanonizedTerm
  {
    def getType: Type = getSystemFType(canon, Γ)

    override def getTerm: Term =
      new FTermGlobalRenaming(names)(canon)
  }

  trait FTermVisitor[T] extends TermVisitor[T] {
    def χ(name: Name): T
    def λ(name: Name, body: T): T
    def ε(operator: T, operand: T): T
    def Λ(alpha: Name, body: T): T
    def □(term: T, typeArg: Type): T

    override def apply(t: Term): T = t match {
      case SystemF.Λ(alpha, body)   => Λ(alpha, apply(body))
      case SystemF.□(term, typeArg) => □(apply(term), typeArg)
      case _                        => super.apply(t)
    }
  }

  implicit class EraseTypeAbstractionsAndApplications(t: Term) {
    def erase: Term = (new ErasureVisitor)(t)

    class ErasureVisitor
    extends FTermVisitor[Term] with TermReconstruction
    {
      private[this] type T = Term
      def Λ(alpha: Name, body: T): T = body
      def □(term: T, typeArg: Type): T = term
    }
  }

  class FTermGlobalRenaming(f: PartialFunction[Name, Name])
  extends TermGlobalRenaming(f) with FTermVisitor[Term] {
    private[this] type T = Term
    def Λ(alpha: Name, body: T): T =
      SystemF.Λ(alpha, body)

    def □(term: T, typeArg: Type): T =
      SystemF.□(term, typeArg)
  }

  def getSystemFType(canon: Term, Γ: PartialFunction[Name, Type]): Type = {
    import SystemF._
    def loop(canon: Term): Type = canon match {
      case χ(name) =>
        Γ(name)

      case λ(name, body) =>
        Γ(name) →: loop(body)

      case ε(operator, operand) =>
        val σ0 → τ = loop(operator)
        val σ1     = loop(operand)
        if (σ0 != σ1)
          sys error s"""|Operand type mismatch in application $canon:
                        |operator : ${σ0} → ${τ}
                        |operand  : ${σ1}
                        |""".stripMargin
        τ

      case Λ(alpha, body) =>
        ∀(alpha, loop(body))

      case □(term, typeArg) =>
        val ∀(alpha, typeBody) = loop(term)
        typeBody substitute (alpha -> typeArg)
    }
    loop(canon)
  }
}

trait PrettyF extends SystemF with Pretty {
  class SystemFPrettyVisitor
  extends PrettyVisitor
     with FTermVisitor[(String, Int)]
  {
    private[this] type T = (String, Int)

    def Λ(alpha: Name, body: T): T =
      template("Λ%s. %s", priority_Λ, (α(alpha), 0), (body, 1))

    def □(term: T, typeArg: Type): T =
      template("%s [%s]", priority_ε,
        (term, 1),
        ((pretty(typeArg), priority_∞), 0))

    def priority_Λ = priority_λ
    def priority_□ = priority_ε
  }

  override def pretty(t: Term): String =
    (new SystemFPrettyVisitor)(t)._1
}

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
