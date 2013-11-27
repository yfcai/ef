trait SystemF extends TypedTerms with Substitution {
  object SystemF {
    case class Λ(alpha: Name, body: Term) extends Term
    case class □(term: Term, typeArg: Type) extends Term
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

  object FTerm {
    def apply[T <% Type](canon: Term, argTypes: (String, T)*): FTerm =
      FTerm(canon,
            argTypes.map({
              case (s, τ) => (StringLiteral(s), τ : Type)
            })(collection.breakOut): Map[Name, Type],
            Map.empty[Name, Name])
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
  val id = FTerm(Λ("α", λ("x")("x")), "x" -> "α")
}

object TestF extends SystemFExamples with PrettyF {
  def p(t: FTerm) {
    println(pretty(t))
  }

  def main(args: Array[String]) {
    p(id)
  }
}
