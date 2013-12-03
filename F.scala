import scala.language.implicitConversions

trait SystemF
extends TypedTerms
   with Substitution
   with PeelAwayQuantifiers
   with AlphaEquivalence
{
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
        if (! α_equivalent(σ0, σ1))
          sys error s"""|Operand type mismatch in application $canon:
                        |operator : ${σ0} → ${τ}
                        |operand  : ${σ1}
                        |""".stripMargin
        τ

      case Λ(alpha, body) =>
        ∀(alpha, loop(body))

      case □(term, typeArg) =>
        doTypeApp(loop(term), List(typeArg))
    }
    loop(canon)
  }

  def doTypeApp(τ : Type, typeArgs: List[Type]): Type = {
    val (quantifiedNames, typeBody) = listOfQuantifiers(τ, typeArgs.size)
    val accordingToPlan: Map[Name, Type] =
      (quantifiedNames, typeArgs).zipped.map({
        case (name, typeArg) => (name, typeArg)
      })(collection.breakOut)
    typeBody substitute accordingToPlan
  }
}

trait PrettyF extends SystemF with Pretty {
  class SystemFPrettyVisitor(t: FTerm)
  extends PrettyVisitor
     with FTermVisitor[(String, Int)]
  {
    private[this] type T = (String, Int)
    private[this] def lookupName = t.names.withDefault(x => x)
    private[this] def lookupType(id: Name): String = apply(t.Γ(id))._1

    def Λ(alpha: Name, body: T): T =
      template("Λ%s. %s", priority_Λ, (α(alpha), 0), (body, 1))

    def □(term: T, typeArg: Type): T =
      template("%s [%s]", priority_ε,
        (term, 1),
        ((pretty(typeArg), priority_∞), 0))

    /** Add type annotations to lambdas */
    override def λ(id: Name, body: T): T =
      template("λ%s. %s", priority_λ,
        ((s"${lookupName(id)} : ${lookupType(id)}", priority_∞), 0),
         (body, 1))

    /** Do renaming on variables */
    override def χ(id: Name): T =
      (lookupName(id).toString, priority_∞)

    def priority_Λ = priority_λ
    def priority_□ = priority_ε
  }

  def pretty(t: FTerm): String =
    new SystemFPrettyVisitor(t)(t.canon)._1
}

// hacked-together executable of system F type checker for demo
trait RenamingF extends Renaming with SystemF {
  trait FTermReconstruction
  extends FTermVisitor[Term]
     with TermReconstruction {
    override def Λ(alpha: Name, body: Term): Term = SystemF.Λ(alpha, body)
    override def □(t: Term, typeArg: Type): Term = SystemF.□(t, typeArg)
  }

  class FTermRenaming(f: PartialFunction[Name, Term])
  extends TermRenaming(f) with FTermReconstruction

  implicit class termRenamingOpsF(t : Term) {
    def rename[N <% Name, T <% Term](f: Map[N, T]): Term =
      new FTermRenaming(f map { case (k, v) => (k: Name, v: Term) })(t)
    def rename(f: Map[Name, Name]): Term =
      new FTermRenaming(f map { case (k, v) => (k: Name, χ(v))    })(t)
    def rename[N <% Name, T <% Name](s: (N, T)*): Term =
      rename(Map(s map (p => (p._1: Name, p._2: Name)): _*))
  }
}

object TypeCheckerF
extends ParsingF
   with PrettyF
   with DecimalLiterals
{
  def process(result: List[Expr]): Unit = result foreach {
    case DefExprF(name, term) =>
      println(s"$name : ${pretty(term.getType)}")
      println(s"$name = ${pretty(term)}")
      println()

    case NakedExprF(term) =>
      println(s"${pretty(term)} : ${pretty(term.getType)}")
      println()
  }

  def main(args: Array[String]) {
    val content: String = try {
      val Array(filename) = args
      val source = scala.io.Source.fromFile(filename)
      val content = source.getLines mkString "\n"
      source.close()
      content
    }
    catch { case e: Throwable =>
      Console.err.println(
        """|Usage: <this-command> <one-single-file>
           |""".stripMargin)
      sys exit -1
    }

    process(parseModule(content))
  }

  object parseModule extends ParserF {
    lazy val moduleParser = module(decimalLiteral)

    def apply(content: String): List[Expr] =
      useParser(moduleParser)(content).get
  }

  type Expr       = parseModule.Expr
  type DefExprF   = parseModule.DefExprF
  val  DefExprF   = parseModule.DefExprF
  type NakedExprF = parseModule.NakedExprF
  val  NakedExprF = parseModule.NakedExprF
}
