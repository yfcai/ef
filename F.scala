import scala.language.implicitConversions

trait SystemF extends TypedTerms with Substitution {
  object SystemF {
    case class Λ(alpha: Name, body: Term) extends Term
    case class □(term: Term, typeArg: Type) extends Term

    object Λ {
      def apply(typeVars: Iterable[Name])(body: => Term): Term =
        if (typeVars.isEmpty)
          body
        else
          Λ(typeVars.head, apply(typeVars.tail)(body))
    }

    object □ {
      def apply(term: Term, typeArgs: Seq[Type]): Term =
        if (typeArgs.isEmpty)
          term
        else
          apply(□(term, typeArgs.head), typeArgs.tail)
    }
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
