import scala.language.higherKinds
import scala.language.implicitConversions

trait FreshNames {
  type Name = String

  def getFreshName(default: Name, toAvoid: Set[Name]): Name = {
    var result = default
    var i = 0
    while (toAvoid contains result) {
      i += 1 ; if (i <= 0) sys error "We ran out of names"
      result = default + i
    }
    result
  }

  private[this] var index = 0
  def getGenerativeName: Name = {
    index += 1
    if (index == 0) sys error "We ran out of generative names"
    "?" + index
  }

  trait Named { def name: Name }
  trait Binding extends Named
  trait Bound   extends Named
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

  case class ∀(name: Name, body: Type) extends Type with Binding
  case class →(domain: Type, range: Type) extends Type
  case class α(name: Name) extends Type with Bound
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
    def ₋ (operand: Term): Term =
      topLevel.ε(operator, operand)
  }

  implicit def nameToVariable(s: Name): Term = χ(s)

  case class χ(name: Name) extends Term with Bound // looks like x
  case class λ(name: Name, body: Term) extends Term with Binding
  case class ε(operator: Term, operand: Term) extends Term // εφαρμογή

  case object Σ extends Term // summation of 2 numbers
  case class  ϕ(value: Int) extends Term // ϕυσικός αριθμός

  trait TermVisitor[T] {
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

trait TypesAndTerms extends Terms with Types {
  trait Visitor[T] extends TypeVisitor[T] with TermVisitor[T] {
    override def ∀(name: Name, body: T): T
    override def →(domain: T, range: T): T
    override def α(name: Name): T
    override def ℤ : T

    override def χ(name: Name): T
    override def λ(name: Name, body: T): T
    override def ε(operator: T, operand: T): T

    override def ϕ(value: Int): T
    override def Σ : T
  }
}

trait Pretty extends TypesAndTerms {
  trait PrettyVisitor extends Visitor[(String, Int)]
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

trait Reconstruction extends TypesAndTerms {
  topLevel =>

  trait TypeReconstruction
  extends TypeVisitor[Type]
  {
    override def ∀(name: Name, body: Type): Type = topLevel.∀(name, body)
    override def →(domain: Type, range: Type): Type = topLevel.→(domain, range)
    override def α(name: Name): Type = topLevel.α(name)
    override def ℤ: Type = topLevel.ℤ
  }

  trait TermReconstruction
  extends TermVisitor[Term]
  {
    override def χ(name: Name): Term = topLevel.χ(name)
    override def λ(name: Name, body: Term): Term = topLevel.λ(name, body)
    override def ε(f: Term, x: Term): Term = topLevel.ε(f, x)

    override def ϕ(value: Int): Term = topLevel.ϕ(value)
    override def Σ : Term = topLevel.Σ
  }
}

trait Holes extends TypesAndTerms with Reconstruction {
  object Hole {
    def spawn(howMany: Int): Iterable[Hole] =
      (0 until howMany) map Hole.apply
  }

  case class Hole(index: Int) extends Type with Term

  trait TypeHoleVisitor[T] extends TypeVisitor[T] {
    def holeInType(hole: Hole): T
    override def apply(τ : Type): T = τ match {
      case hole: Hole => holeInType(hole)
      case _ => super.apply(τ)
    }
  }
  trait TermHoleVisitor[T] extends TermVisitor[T] {
    def holeInTerm(hole: Hole): T
    override def apply(t : Term): T = t match {
      case hole: Hole => holeInTerm(hole)
      case _ => super.apply(t)
    }
  }

  trait TypeHoleReconstruction
  extends TypeHoleVisitor[Type] with TypeReconstruction {
    override def holeInType(holeID: Hole) = holeID.asInstanceOf[Type]
  }

  trait TermHoleReconstruction
  extends TermHoleVisitor[Term] with TermReconstruction {
    override def holeInTerm(holeID: Hole) = holeID.asInstanceOf[Term]
  }

  object SubstantiationViaHoles
  {
    class TypeVisitor(f: Hole => Type)
    extends TypeHoleVisitor[Type] with TypeReconstruction
    { override def holeInType(hole: Hole) = f(hole) }
    class TermVisitor(f: Hole => Term)
    extends TermHoleVisitor[Term] with TermReconstruction
    { override def holeInTerm(hole: Hole) = f(hole) }
  }

  implicit class typeSubstantiationOps(τ : Type) {
    def <<(f: Hole => Type): Type =
      new SubstantiationViaHoles.TypeVisitor(f)(τ)
  }
  implicit class termSubstantiationOps(t : Term) {
    def <<(f: Hole => Term): Term =
      new SubstantiationViaHoles.TermVisitor(f)(t)
  }
}

/** Renaming is not compositional. */
trait Renaming extends Holes {
  topLevel =>

  implicit class UndefinePartialFunction[S, T]
                 (f: PartialFunction[S, T]) {
    def undefine(s: S): PartialFunction[S, T] = f match {
      case map: Map[_, _] => map - s
      case _ => new PartialFunction[S, T] {
        override def isDefinedAt(x: S): Boolean =
          if (x == s) false
          else        f.isDefinedAt(x)
        override def apply(x: S): T =
          if (x == s) sys error s"AAAAHHH UNDEFINED $x"
          else        f(x)
      }
    }
  }

  class TypeRenaming(f: PartialFunction[Name, Type])
  extends TypeHoleReconstruction {
    override def α(name: Name): Type =
      if (f.isDefinedAt(name)) f(name)
      else super.α(name)
    override def apply(τ : Type): Type = τ match {
      case ∀(name, body) if (f.isDefinedAt(name)) =>
        super.∀(name, new TypeRenaming(f undefine name) apply body)
      case _ => super.apply(τ)
    }
  }

  class TermRenaming(f: PartialFunction[Name, Term])
  extends TermHoleReconstruction {
    override def χ(name: Name): Term =
      if (f.isDefinedAt(name)) f(name)
      else super.χ(name)
    override def apply(t : Term): Term = t match {
      case λ(name, body) if (f.isDefinedAt(name)) =>
        super.λ(name, new TermRenaming(f undefine name) apply body)
      case _ => super.apply(t)
    }
  }

  implicit class typeRenamingOps(τ : Type) {
    def rename(f: PartialFunction[Name, Type]): Type =
      new TypeRenaming(f)(τ)
  }
  implicit class termRenamingOps(t : Term) {
    def rename(f: PartialFunction[Name, Term]): Term =
      new TermRenaming(f)(t)
  }
}

trait GlobalRenaming extends Renaming {
  class TypeGlobalRenaming(f: PartialFunction[Name, Name])
  extends TypeRenaming(f andThen α) with TypeReconstruction
  {
    override def apply(τ : Type): Type = τ match {
      case ∀(name, body) =>
        super[TypeReconstruction].
          ∀(f.applyOrElse[Name, Name](name, _ => name), apply(body))
      case _ => super.apply(τ)
    }
  }
  class TermGlobalRenaming(f: PartialFunction[Name, Name])
  extends TermRenaming(f andThen χ) with TermReconstruction
  {
    override def apply(t : Term): Term = t match {
      case λ(name, body) =>
        super[TermReconstruction].
          λ(f.applyOrElse[Name, Name](name, _ => name), apply(body))
      case _ => super.apply(t)
    }
  }

  implicit class typeBoudRenamingOps(τ : Type) {
    def renameAll(f: PartialFunction[Name, Name]): Type =
      new TypeGlobalRenaming(f)(τ)
  }
  implicit class termBoundRenamingOps(t : Term) {
    def renameAll(f: PartialFunction[Name, Name]): Term =
      new TermGlobalRenaming(f)(t)
  }
}

trait FreeNames extends TypesAndTerms {
  object getFreeNames extends Visitor[Set[Name]] {
    private[this] type T = Set[Name]
    override def ∀(name: Name, body: T) = body - name
    override def →(domain: T, range: T) = domain ++ range
    override def α(name: Name) = Set(name)
    override def ℤ = Set.empty

    override def χ(name: Name) = Set(name)
    override def λ(name: Name, body: T) = body - name
    override def ε(operator: T, operand: T) = operator ++ operand

    override def ϕ(value: Int) = Set.empty
    override def Σ = Set.empty
  }
}

trait Substitution extends GlobalRenaming with Holes with FreeNames {
  def substituteInType(τ : Type, f : Map[Name, Type]): Type = {
    // 1. Rename target variables to holes
    val withDrills: Map[Name, Hole] =
      (f, Hole.spawn(f.size)).zipped.map({
        case ((name, newType), hole) => (name, hole)
      })(collection.breakOut)
    val holesDrilled =
      τ rename withDrills
    // 2. Rename bound variables who capture free names
    //    (those one has to rename are precisely those to avoid)
    val freeNames =
      (f map { kv => getFreeNames(kv._2) }).fold(Set.empty)(_ ++ _)
    val withFresheners: Map[Name, Name] =
      freeNames.map(
        name => (name, getFreshName(name, freeNames))
      )(collection.breakOut)
    val freshened = holesDrilled renameAll withFresheners
    // 3. Substantiate by filling holes
    val forGreatJustice: Map[Hole, Type] =
      f map { case (name, newType) => (withDrills(name), newType) }
    freshened << forGreatJustice
  }
  def substituteInTerm(t : Term, f : Map[Name, Term]): Term = {
    // 1. Rename target variables to holes
    val withDrills: Map[Name, Hole] =
      (f, Hole.spawn(f.size)).zipped.map({
        case ((name, newType), hole) => (name, hole)
      })(collection.breakOut)
    val holesDrilled =
      t rename withDrills
    // 2. Rename bound variables who capture free names
    //    (those one has to rename are precisely those to avoid)
    val freeNames =
      (f map { kv => getFreeNames(kv._2) }).fold(Set.empty)(_ ++ _)
    val withFresheners: Map[Name, Name] =
      freeNames.map(
        name => (name, getFreshName(name, freeNames))
      )(collection.breakOut)
    val freshened = holesDrilled renameAll withFresheners
    // 3. Substantiate by filling holes
    val forGreatJustice: Map[Hole, Term] =
      f map { case (name, newTerm) => (withDrills(name), newTerm) }
    freshened << forGreatJustice
  }

  implicit class typeSubstitutionOps(τ : Type) {
    def substitute[T <% Type](scheme: (Name, T)*): Type =
      substitute(Map(scheme map {kv => (kv._1, kv._2: Type)}: _*))
    def substitute(scheme: Map[Name, Type]): Type =
      substituteInType(τ, scheme)
  }
  implicit class termSubstitutionOps(t : Term) {
    def substitute[T <% Term](scheme: (Name, T)*): Term =
      substitute(Map(scheme map {kv => (kv._1, kv._2: Term)}: _*))
    def substitute(scheme: Map[Name, Term]): Term =
      substituteInTerm(t, scheme)
  }
}

// reader monad?
trait TypedTerms extends TypesAndTerms {
  case class TypedTerm(term: Term, getType: Type, subterms: TypedTerm*) {
    def fold[B](f: (Term, Type, B*) => B): B =
      f(term, getType, subterms map (_ fold f): _*)
  }
}

trait Unification extends Substitution with TypedTerms {
  import collection.immutable.HashMap
  type Context = HashMap[Name, Type]
  val ∅ : Context = HashMap.empty
  implicit def singletonToContext(p: (Name, Type)): Context = HashMap(p)

  case class Judgement(Γ : Context, t : Term, τ : Type)

  case class EqConstraint(lhs: Type, rhs: Type)

  class U01_GatherConstraints
  extends TermVisitor[(Judgement, List[EqConstraint], List[Type])] {
    private[this] type T = (Judgement, List[EqConstraint], List[Type])

    // could have used prealgebra composition with Reconstruction
    private[this] object R extends TermReconstruction

    def χ(name: Name): T = {
      val τ = α(getGenerativeName)
      (Judgement(name -> τ, R.χ(name), τ), Nil, Nil)
    }

    def λ(name: Name, body: T): T = {
      val (Judgement(_Γ, t, τ), constraints, typeArgs) = body
      val σ = _Γ.applyOrElse[Name, Type](name, _ => α(getGenerativeName))
      (Judgement(_Γ - name, R.λ(name, t), σ →: τ), constraints,
        σ :: typeArgs)
    }

    def ε(operator: T, operand: T): T = {
      val (Judgement(f_Γ, f, f_τ), f_constraints, f_typeArgs) = operator
      val (Judgement(x_Γ, x, σ  ), x_constraints, x_typeArgs) = operand
      val τ = α(getGenerativeName)
      val Γ = (f_Γ merged x_Γ) { case ((name, τ1), _) => (name, τ1) }
      val constraints = EqConstraint(f_τ, σ →: τ) :: (
        f_constraints ++ x_constraints ++
          f_Γ.filter(x_Γ contains _._1).map({
            case (name, τ1) => EqConstraint(τ1, x_Γ(name))
          })
      )
      (Judgement(Γ, R.ε(f, x), τ), constraints,
        // Argument order of ++ is very important!
        // Since hidden type arguments are prepended in evaluation order,
        // the subterm f that's evaluated first contributes to a later
        // part of the list of hidden arguments.
        x_typeArgs ++ f_typeArgs)
    }

    def ϕ(value: Int): T = (Judgement(∅, R.ϕ(value), ℤ), Nil, Nil)
    def Σ : T = (Judgement(∅, R.Σ, ℤ →: ℤ →: ℤ), Nil, Nil)
  }

  def U02_MGS(constraints: List[EqConstraint]):
      Option[Map[Name, Type]] = {
    type Eq = EqConstraint
    val  Eq = EqConstraint
    constraints match {
      case Nil =>
        Some(Map.empty)

      case Eq(σ1 → τ1, σ2 → τ2) :: others =>
        U02_MGS(Eq(σ1, σ2) :: Eq(τ1, τ2) :: others)

      case Eq(α(name), τ) :: others =>
        U02_MGS(others map { case Eq(τ1, τ2) =>
          Eq(τ1 substitute (name -> τ),
             τ2 substitute (name -> τ))
        }) map { mgs => mgs.updated(name, τ substitute mgs) }

      case Eq(τ, α(name)) :: others =>
        U02_MGS(Eq(α(name), τ) :: others)

      case _ =>
        None
    }
  }

  class U03_Inference(
    mostGeneralSubstitution: Map[Name, Type],
    judgements: List[Judgement]
  )
  extends TermVisitor[TypedTerm]
  {
    val mgs = mostGeneralSubstitution.orElse[Name, Type] {
      case name => α(name)
    }

    private[this] type T = TypedTerm
    def χ(name: Name): T = ???
    def λ(name: Name, body: T): T = ???
    def ε(operator: T, operand: T): T = ???

    def ϕ(value: Int): T = ???
    def Σ : T = ???
  }
}

/*
trait Unification extends TypesAndTerms with UntypedTerms {
  case class Unify(lhs: Type, rhs: Type) {
    override def toString: String = s"$lhs == $rhs"
  }

  // Run into expression problem in the language of types.
  // TODO take other type constructors into consideration
  // in ₋freeTypeVars₋ and ₋tsub₋... or just use ₋Product₋
  // and ₋isInstanceOf₋.

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
  // Without Meh, ₋const₋ is not typeable with a minimally
  // quantified type.
  case object Meh extends Type
}

trait WeirdCalculus extends UntypedTerms with MinimallyQuantifiedTypes {
}

 */

object TestEverything
//extends WeirdCalculus with Unification {
extends Pretty with Substitution {
  def main(args: Array[String]) {
    val hole1 = Hole.spawn(1).head
    val hole2 = Hole.spawn(1).head
    val s = λ("x", "y") { Σ ₋ hole1 ₋ "z" }
    val σ = "r" →: ∀("r", "a" →: "r") →: hole2 →: "r"
    val t = (s << Map(hole1 -> (Σ ₋ "x" ₋ "y"))) rename
      Map("y" -> "a", "z" -> "b") renameAll
      Map("x" -> "k", "b" -> "c") substitute
      ("y" -> χ("x"), "c" -> "k" ₋ "k1")
    val τ = (σ << Map(hole2 -> ℤ)) renameAll
      Map("r" -> "α") substitute
      ("α" -> "β", "a" -> "α")
    println(pretty(t))
    println(pretty(τ))
    //val term = inferSimpleType(untypedTerm)
    //println(s"Unification works!")
    //println(s"type = ${term.getType}")
    //println(s"term = $term")
  }
}
