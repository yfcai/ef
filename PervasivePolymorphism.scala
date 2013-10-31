import scala.language.implicitConversions

trait SimpleTypes { topLevel =>
  trait Type

  case class →:(domain: Type, range: Type) extends Type {
    override def toString = domain match {
      case _ →: _ => s"($domain) → $range"
      case _      => s"$domain → $range"
    }
  }
  implicit class FunctionTypeOps(range: Type) {
    def →:(domain: Type): Type = topLevel.→:(domain, range)
  }
}

trait FreshNames {
  type Name = String

  private var count: Int = -1

  def getFreshName(tentative: Name): Name = {
    count += 1
    if (count < 0) sys error "Namespace overflown"
    tentative + count
  }
}

trait TypedTerms extends SimpleTypes with FreshNames {
  trait Term {
    def getType: Type

    // DO NOT forces early failure!
    // unification can create ill-typed intermediate terms!
    // assert(getType != null)
  }

  case class Var(name: Name, getType: Type) extends Term

  case class Abs(parameter: Var, body: Term) extends Term {
    def getType: Type = parameter.getType →: body.getType
  }

  case class App(operator: Term, operand: Term) extends Term {
    def getType: Type = operator.getType match {
      case domain →: range if domain == operand.getType =>
        range
    }
  }

  case object ℤ extends Type

  case class ℤ(value: Int) extends Term {
    def getType: Type = ℤ
  }

  case object Plus extends Term {
    def getType: Type = ℤ →: ℤ →: ℤ
  }
}

// types with type variables and foralls
trait QuantifiedTypes extends SimpleTypes with FreshNames {
  case class TypeVar(name: Name) extends Type {
    override def toString = name.toString
  }

  case class ∀(boundTypeVar: TypeVar, body: Type) extends Type

  object ∀ {
    def apply(names: Name*)(body: => Type): ∀ =
      if (names.size <= 1)
        ∀(TypeVar(names.head), body)
      else
        ∀(TypeVar(names.head), ∀(names.tail: _*)(body))
  }
}

trait UntypedTerms extends TypedTerms with QuantifiedTypes {
  topLevel =>

  sealed trait UntypedTerm

  case class ForgetfulTerm(toTerm: Term) extends UntypedTerm {
    override def toString: String = toTerm.toString
  }
  implicit def termToUntypedTerm(t0: Term): UntypedTerm =
    ForgetfulTerm(t0)

  case class UntypedVar(name: Name) extends UntypedTerm {
    override def toString: String = name.toString
  }
  implicit def nameToUntypedVar(name: Name): UntypedTerm =
    UntypedVar(name)

  // for a pretty-ish print-out
  // I feel bad for not print according to operator precedence
  def unparenthesize(x: Any): String = {
    val s = x.toString
    if ((s startsWith "(") && (s endsWith ")"))
      s.substring(1, s.length - 1)
    else
      sys error s"Unparenthesizing something that ain't parenthesized: $s"
  }

  case class λ(parameter: Name, body: UntypedTerm) extends UntypedTerm {
    override def toString: String = body match {
      case λ(_, _) | _ ! _ =>
        val bd = body.toString
        s"(λ$parameter. ${unparenthesize(body)})"

      case _ =>
        s"(λ$parameter. $body)"
    }
  }

  object λ {
    def apply(args: Name*)(body: => UntypedTerm): λ =
      if(args.size <= 1)
        λ(args.head, body)
      else
        λ(args.head, apply(args.tail: _*)(body))
  }

  case class !(operator: UntypedTerm, operand: UntypedTerm)
  extends UntypedTerm {
    override def toString: String = operator match {
      case _ ! _ =>
        s"(${unparenthesize(operator)} $operand)"

      case _ =>
        s"($operator $operand)"
    }
  }
  implicit class polymorphicAppOps[T <% UntypedTerm](operator: T) {
    def ! (operand: UntypedTerm): UntypedTerm =
      topLevel.!(operator, operand)
  }
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

object TestEverything extends WeirdCalculus with Unification {
  def main(args: Array[String]) {
    val untypedTerm = λ("x", "y", "z") { Plus ! (Plus ! "x" ! "y") ! "z" }
    val term = inferSimpleType(untypedTerm)
    println(s"Unification works!")
    println(s"type = ${term.getType}")
    println(s"term = $term")
  }
}
