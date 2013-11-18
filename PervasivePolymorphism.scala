import scala.language.implicitConversions

trait FreshNames {
  type Name = String

  private var count: Int = -1

  def getFreshName(tentative: Name): Name = {
    count += 1
    if (count < 0) sys error "Namespace overflown"
    tentative + count
  }
}

trait Types extends FreshNames {
  topLevel =>

  trait Type

  implicit class FunctionTypeOps[T <% Type](range: T) {
    def →:(domain: Type): Type = topLevel.→(domain, range)
  }

  object ∀ {
    def apply(names: Name*)(body: => Type): ∀ =
      if (names.size <= 1)
        ∀(names.head, body)
      else
        ∀(names.head, ∀(names.tail: _*)(body))
  }

  implicit def nameToTypeVariable(s: Name): Type = α(s)

  case class ∀(name: Name, body: Type) extends Type
  case class →(domain: Type, range: Type) extends Type
  case class α(name: Name) extends Type
  case object ℤ extends Type

  trait TypeVisitor[T] {
    def ∀(name: Name, body: T): T
    def →(domain: T, range: T): T
    def α(name: Name): T
    def ℤ : T

    def apply(τ : Type): T = τ match {
      case topLevel.∀(name, body)    => ∀(name, apply(body))
      case topLevel.→(domain, range) => →(apply(domain), apply(range))
      case topLevel.α(name)          => α(name)
      case topLevel.ℤ                => ℤ
    }
  }
}

trait Terms extends FreshNames with Types {
  topLevel =>

  trait Term

  object λ {
    def apply(args: Name*)(body: => Term): λ =
      if(args.size <= 1)
        λ(args.head, body)
      else
        λ(args.head, apply(args.tail: _*)(body))
  }

  implicit class untypedAppOps[T <% Term](operator: T) {
    def ε (operand: Term): Term =
      topLevel.ε(operator, operand)
  }

  implicit def nameToVariable(s: Name): Term = χ(s)

  case class χ(name: Name) extends Term
  case class λ(parameter: Name, body: Term) extends Term
  case class ε(operator: Term, operand: Term) extends Term

  case object Σ extends Term
  case class  ϕ(value: Int) extends Term // ϕυσικός αριθμός

  trait Visitor[T] {
    def χ(name: Name): T
    def λ(name: Name, body: T): T
    def ε(operator: T, operand: T): T

    def ϕ(value: Int): T
    def Σ : T

    def apply(t: Term): T = t match {
      case topLevel.χ(name)       => χ(name)
      case topLevel.λ(name, body) => λ(name, apply(body))
      case topLevel.ε(fun, arg)   => ε(apply(fun), apply(arg))

      case topLevel.ϕ(value)      => ϕ(value)
      case topLevel.Σ             => Σ
    }
  }
}

trait Pretty extends Terms with Types {
  trait PrettyVisitor
  extends Visitor[(String, Int)]
     with TypeVisitor[(String, Int)]
  {
    private type Domain = (String, Int)

    override def ∀(name: Name, body: Domain) = body match {
      case (body, pBody) =>
        ("∀%s. %s".format(
          name.toString,
          paren(pBody, priority_∀ + 1, body)
        ), priority_∀)
    }

    override def →(σ : Domain, τ : Domain) = (σ , τ) match {
      case ((σ, priority_σ), (τ, priority_τ)) =>
        ("%s → %s".format(
          paren(priority_σ, priority_→,     σ),
          paren(priority_τ, priority_→ + 1, τ)
        ), priority_→)
    }

    override def α(name: Name) = (name.toString, priority_↓)
    override def ℤ = ("ℤ", priority_↓)

    def χ(name: Name): Domain = (name.toString, priority_↓)

    override def λ(name: Name, body: Domain): Domain = body match {
      case (body, pBody) =>
        ("λ%s. %s".format(
          name.toString,
          paren(pBody, priority_λ + 1, body)
        ), priority_λ)
    }

    override def ε(f: Domain, x: Domain) = (f, x) match {
      case ((f, pf), (x, px)) =>
        ("%s %s".format(
          paren(pf, priority_ε + 1, f),
          paren(px, priority_ε,     x)
        ), priority_ε)
    }

    override def ϕ(value: Int) = (value.toString, priority_↓)
    override def Σ = ("Σ", priority_↓)

    val priority_↑ = 3 // outermost priority
    val priority_λ = 2
    val priority_∀ = 2
    val priority_ε = 1
    val priority_→ = 1
    val priority_↓ = 0

    def paren(innerPriority: Int, outerPriority: Int, text: String):
        String =
      if (innerPriority < outerPriority)
        text
      else
        "(%s)" format text
  }

  object PrettyVisitor extends PrettyVisitor

  def pretty(t : Term): String = PrettyVisitor(t)._1
  def pretty(τ : Type): String = PrettyVisitor(τ)._1
}

/*
// types with type variables and foralls
trait QuantifiedTypes extends TypeVars {
}

trait Unification extends TypedTerms with UntypedTerms {
  case class Unify(lhs: Type, rhs: Type) {
    override def toString: String = s"$lhs == $rhs"
  }

  // Run into expression problem in the language of types.
  // TODO take other type constructors into consideration
  // in `freeTypeVars` and `tsub`... or just use `Product`
  // and `isInstanceOf`.

  def freeTypeVars(tau: Type): Set[TypeVar] = tau match {
    case x @ TypeVar(_) =>
      Set(x)

    case ∀(boundTypeVar, body) =>
      freeTypeVars(body) - boundTypeVar

    case σ →: τ =>
      freeTypeVars(σ) ++ freeTypeVars(τ)

    case _ =>
      Set.empty
  }
  implicit class typeVarDotIsFreeIn(x: TypeVar) {
    def isFreeIn(tau: Type): Boolean =
      freeTypeVars(tau) contains x
  }

  def tsubAll(subs: Map[TypeVar, Type], tau: Type): Type =
    subs.foldRight(tau) { (keyValuePair, wipType) =>
      val (x, σ) = keyValuePair
      tsub(x, σ, wipType)
    }

  // capture avoidance...
  def tsub(x: TypeVar, tau: Type, body: Type): Type = body match {
    case y @ TypeVar(_) if x == y =>
      tau

    // premature optimization
    case quantifiedType @ ∀(boundTypeVar, body)
        if tau.isInstanceOf[TypeVar] =>
      if (tau == boundTypeVar)
        quantifiedType
      else
        ∀(boundTypeVar, tsub(x, tau, body))

    case ∀(boundTypeVar, body) =>
      if (boundTypeVar isFreeIn tau) {
        val newBoundTypeVar = TypeVar(getFreshName(boundTypeVar.name))
        ∀(newBoundTypeVar,
          tsub(x, tau,
            tsub(boundTypeVar, newBoundTypeVar, body)))
      }
      else
        ∀(boundTypeVar, tsub(x, tau, body))

    case σ →: τ =>
      tsub(x, tau, σ) →: tsub(x, tau, τ)

    case _ => body
  }

  type Constraints = List[Unify]
  type TypingContext = Map[Name, Type]

  def getUnificationConstraints(t: UntypedTerm):
      (Type, Term, Constraints) = {
    // ∅ is an operator symbol, not a letter, thus the space before colon.
    val ∅ : TypingContext = Map.empty
    def loop(t: UntypedTerm, Γ: TypingContext):
        (Type, Term, Constraints) =
      t match {
        case ForgetfulTerm(t) =>
          (t.getType, t, Nil)

        case UntypedVar(x) =>
          (Γ(x), Var(x, Γ(x)), Nil)

        case λ(x, body) =>
          val σ = TypeVar(getFreshName("σ"))
          val (τ, typedBody, constraints) = loop(body, Γ.updated(x, σ))
          (σ →: τ, Abs(Var(x, σ), typedBody), constraints)

        case operator ! operand =>
          val τ = TypeVar(getFreshName("τ"))
          val (operatorType, typedOperator, acc0) =
            loop(operator, Γ)
          val (operandType, typedOperand, acc1) =
            loop(operand, Γ)
          ( τ,
            App(typedOperator, typedOperand),
            Unify(operatorType, operandType →: τ) :: (acc0 ++ acc1) )
      }
    loop(t, ∅)
  }

  def getMostGeneralSubstitutions(constraints: Constraints):
      Map[TypeVar, Type] = constraints match {
    case Nil =>
      Map.empty

    case (unify @ Unify(σ, τ)) :: constraints
        if σ.isInstanceOf[TypeVar] || τ.isInstanceOf[TypeVar] =>
      val (x, body) = (σ, τ) match {
        case (x @ TypeVar(_), _) => (x, τ)
        case (_, y @ TypeVar(_)) => (y, σ)
      }
      if (x isFreeIn body)
        sys error s"Type variable $x appears on both sides of $unify"
      else {
        val mgss = getMostGeneralSubstitutions(constraints map {
          case Unify(a, b) =>
            Unify(tsub(x, body, a), tsub(x, body, b))
        })
        val xType = tsubAll(mgss, body)
        mgss.updated(x, xType)
      }

    case Unify(a →: b, c →: d) :: constraints =>
      getMostGeneralSubstitutions(Unify(a, c) :: Unify(b, d) :: constraints)

    case Unify(a, b) :: constraints if a == b =>
      getMostGeneralSubstitutions(constraints)
  }

  def inferSimpleType(t0: UntypedTerm): Term = {
    val (τ, t, constraints) = getUnificationConstraints(t0)
    val mgss = getMostGeneralSubstitutions(constraints)
    def useMGSS(τ: Type): Type = tsubAll(mgss, τ)
    def applyMGSS(t: Term): Term = t match {
      case Var(x, τ) =>
        Var(x, useMGSS(τ))

      case Abs(Var(x, τ), body) =>
        Abs(Var(x, useMGSS(τ)), applyMGSS(body))

      case App(operator, operand) =>
        App(applyMGSS(operator), applyMGSS(operand))

      case _ =>
        t
    }
    applyMGSS(t)
  }
}

trait MinimallyQuantifiedTypes extends QuantifiedTypes {
  // A quantified type is minimally quantified if every quantifier
  // attaches to the least common ancestor of all occurrences of
  // the type variable it binds.

  // Meh. Whatever. Don't care.
  //
  // If Meh occurs somewhere in the type of a term, then that term
  // puts no constraint whatsoever upon the type of that argument.
  //
  // If Meh is the argument type, then the argument is ignored.
  //
  // If Meh is the result type, then it's equivalent to (∀τ. τ).
  //
  // Without Meh, `const` is not typeable with a minimally
  // quantified type.
  case object Meh extends Type
}

trait WeirdCalculus extends UntypedTerms with MinimallyQuantifiedTypes {
}

 */

object TestEverything
//extends WeirdCalculus with Unification {
extends Pretty {
  def main(args: Array[String]) {
    val t = λ("x", "y", "z") { Σ ε (Σ ε "x" ε "y") ε "z" }
    val τ = "r" →: ("r" →: "r") →: ℤ →: "r"
    println(pretty(t))
    println(pretty(τ))
    //val term = inferSimpleType(untypedTerm)
    //println(s"Unification works!")
    //println(s"type = ${term.getType}")
    //println(s"term = $term")
  }
}
