import scala.language.higherKinds
import scala.language.implicitConversions

trait FreshNames {
  trait Name
  trait Named { def name: Name }
  trait Binding extends Named
  trait Bound   extends Named

  case class NameLiteral(override val toString: String) extends Name

  case class ID(index: Int) extends Name {
    override def toString = "?" + index
  }

  implicit def stringToNameLiteral(s: String): Name = NameLiteral(s)

  def getFreshName(default: Name, toAvoid: Set[Name]): Name = {
    val cons: Int => Name = default match {
      case NameLiteral(s) => i => s + i
      case ID(_)          => i => ID(i)
    }
    val startingID: Int = default match {
      case NameLiteral(_) => 0
      case ID(j)          => j
    }
    var i = startingID
    var result = default
    while (toAvoid contains result) {
      i += 1 ; if (i == startingID) sys error "We ran out of names"
      result = cons(i)
    }
    result
  }

  def getFreshIDs(howMany: Int, toAvoid: Set[Name]): Set[Name] = {
    def loop(start: Int, howMany: Int, toAvoid: Set[Name]): Set[Name] =
      if (howMany <= 0)
        Set.empty
      else {
        var i = start
        while(toAvoid contains ID(i)) i += 1
        loop(i + 1, howMany - 1, toAvoid + ID(i)) + ID(i)
      }
    loop(0, howMany, toAvoid)
  }

  class GenerativeNameGenerator {
    var index: Int = -1
    val alpha: Int = 0x000003B1

    def next: Name = {
      index = index + 1
      if (index == -1) sys error "We ran out of generative names"
      val bytes = Seq(0xFF, 0xFF00, 0xFF0000, 0xFF0000).zipWithIndex map {
        // >>> is    logical shift
        // >>  is arithmetic shift
        case (mask, i) => (index & mask) >>> (i * 8)
      }
      val length = bytes.length - bytes.reverse.prefixLength(_ == 0)
      bytes.slice(0, Math.max(1, length)).
        map(byte => (alpha + byte).asInstanceOf[Char]).mkString
    }

/* better version
    def next: Name = {
      index = index + 1
      if (index == -1) sys error "We ran out of generative names"
      ID(index)
    }
 */
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

  implicit def stringToTypeVariable(s: String): Type = α(s)

  case class ∀(name: Name, body: Type) extends Type with Binding
  case class →(domain: Type, range: Type) extends Type
  case class α(name: Name) extends Type with Bound
  case class ★(operator: Type, operand: Type) extends Type
  case object ? extends Type

  trait TypeVisitor[T] {
    def ∀(name: Name, body: T): T
    def →(domain: T, range: T): T
    def α(name: Name): T
    def ★(operator: T, operand: T): T
    def ? : T

    def apply(τ : Type): T = τ match {
      case topLevel.∀(name, body)    => ∀(name, apply(body))
      case topLevel.→(domain, range) => →(apply(domain), apply(range))
      case topLevel.α(name)          => α(name)
      case topLevel.★(f, x)          => ★(apply(f), apply(x))
      case topLevel.?                => ?
    }
  }
}

trait Terms extends FreshNames with Types {
  topLevel =>

  trait Term

  object λ {
    def apply(args: String*)(body: => Term): λ =
      if(args.size <= 1)
        λ(args.head, body)
      else
        λ(args.head, apply(args.tail: _*)(body))
  }

  implicit class untypedAppOps[T <% Term](operator: T) {
    def ₋ (operand: Term): Term =
      topLevel.ε(operator, operand)
  }

  implicit def stringToVariable(s: String): Term = χ(s)

  case class χ(name: Name) extends Term with Bound // looks like x
  case class λ(name: Name, body: Term) extends Term with Binding
  case class ε(operator: Term, operand: Term) extends Term // εφαρμογή

  trait TermVisitor[T] {
    def χ(name: Name): T
    def λ(name: Name, body: T): T
    def ε(operator: T, operand: T): T

    def apply(t: Term): T = t match {
      case topLevel.χ(name)       => χ(name)
      case topLevel.λ(name, body) => λ(name, apply(body))
      case topLevel.ε(fun, arg)   => ε(apply(fun), apply(arg))
    }
  }
}

trait TypesAndTerms extends Terms with Types {
  trait Visitor[T] extends TypeVisitor[T] with TermVisitor[T] {
    def ∀(name: Name, body: T): T
    def →(domain: T, range: T): T
    def α(name: Name): T
    def ? : T
    def ★(operator: T, operand: T): T

    def χ(name: Name): T
    def λ(name: Name, body: T): T
    def ε(operator: T, operand: T): T
  }
}

trait Reconstruction extends TypesAndTerms {
  topLevel =>

  trait TypeReconstruction extends TypeVisitor[Type] {
    override def ∀(name: Name, body: Type): Type = topLevel.∀(name, body)
    override def →(domain: Type, range: Type): Type = topLevel.→(domain, range)
    override def α(name: Name): Type = topLevel.α(name)
    override def ? : Type = topLevel.?
    override def ★(typeFun: Type, typeArg: Type) = topLevel.★(typeFun, typeArg)
  }

  trait TermReconstruction extends TermVisitor[Term] {
    override def χ(name: Name): Term = topLevel.χ(name)
    override def λ(name: Name, body: Term): Term = topLevel.λ(name, body)
    override def ε(f: Term, x: Term): Term = topLevel.ε(f, x)
  }

  trait Reconstruction extends TypeReconstruction with TermReconstruction
}

/** Renaming is not compositional. */
trait Renaming extends TypesAndTerms with Reconstruction {
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
  extends TypeReconstruction {
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
  extends TermReconstruction {
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
    def rename[N <% Name, T <% Type](f: Map[N, T]): Type =
      new TypeRenaming(f map { case (k, v) => (k: Name, v: Type) })(τ)
  }
  implicit class termRenamingOps(t : Term) {
    def rename[N <% Name, T <% Term](f: Map[N, T]): Term =
      new TermRenaming(f map { case (k, v) => (k: Name, v: Term) })(t)
  }
}

trait GlobalRenaming extends Renaming {
  class TypeGlobalRenaming(f: PartialFunction[Name, Name])
  extends TypeRenaming(f andThen α) with Reconstruction
  {
    override def apply(τ : Type): Type = τ match {
      case ∀(name, body) =>
        super[Reconstruction].
          ∀(f.applyOrElse[Name, Name](name, _ => name), apply(body))
      case _ => super.apply(τ)
    }
  }
  class TermGlobalRenaming(f: PartialFunction[Name, Name])
  extends TermRenaming(f andThen χ) with Reconstruction
  {
    override def apply(t : Term): Term = t match {
      case λ(name, body) =>
        super[Reconstruction].
          λ(f.applyOrElse[Name, Name](name, _ => name), apply(body))
      case _ => super.apply(t)
    }
  }

  implicit class typeBoudRenamingOps(τ : Type) {
    def renameAll[N <% Name](f: Map[N, N]): Type =
      new TypeGlobalRenaming(f map { case (k, v) => (k: Name, v: Name) })(τ)
  }
  implicit class termBoundRenamingOps(t : Term) {
    def renameAll[N <% Name](f: Map[N, N]): Term =
      new TermGlobalRenaming(f map { case (k, v) => (k: Name, v: Name) })(t)
  }
}

trait FreeNames extends TypesAndTerms {
  object getFreeNames extends Visitor[Set[Name]] {
    private[this] type T = Set[Name]
    def ∀(name: Name, body: T): T = body - name
    def →(domain: T, range: T): T = domain ++ range
    def α(name: Name): T = Set(name)
    def ? : T = Set.empty
    def ★(typeFun: T, typeArg: T) = typeFun ++ typeArg

    def χ(name: Name): T = Set(name)
    def λ(name: Name, body: T): T = body - name
    def ε(operator: T, operand: T): T = operator ++ operand
  }
}

trait CanonicalNames extends FreeNames with Renaming {
  class CollectBindings extends Visitor[List[Name]] {
    private[this] type T = List[Name]

    def ∀(name: Name, body: T): T = name :: body
    def →(domain: T, range: T): T = domain ++ range
    def α(name: Name): T = Nil
    def ? : T = Nil
    def ★(typeFun: T, typeArg: T): T = typeFun ++ typeArg

    def χ(name: Name): T = Nil
    def λ(name: Name, body: T): T = name :: body
    def ε(operator: T, operand: T): T = operator ++ operand
  }

  // Not compositional at the moment.
  // Can be made compositional by enlarging the domain
  // to (Term, Map[Name, Name]), but the lack of prealgebra
  // composition means boilerplates. Hence, for now, I
  // tolerate dirty and shorter code.
  class RenameBindings(newNames: Seq[Name])
  extends TypeReconstruction with TermReconstruction
  {
    private[this] val nameStack =
      collection.mutable.Stack(newNames.reverse: _*)

    override def ∀(name: Name, body: Type): Type = {
      val newName = nameStack.pop
      super.∀(newName, body rename Map(name -> super.α(newName)))
    }

    override def λ(name: Name, body: Term): Term = {
      val newName = nameStack.pop
      super.λ(newName, body rename Map(name -> super.χ(newName)))
    }
  }

  private[this] type R = Map[Name, Name]

  def canonizeNames(τ : Type): (Type, R, R) = {
    val freeNames = getFreeNames(τ)
    val boundNames = (new CollectBindings)(τ)
    val freeInverse: Map[Name, Name] =
      ((0 until freeNames.size), freeNames).zipped.map({
        case (i, name) => ID(i) -> name
      })(collection.breakOut)
    val freeIDs = freeInverse map { case (id, name) => name -> α(id) }
    val boundIDs = (0 until boundNames.size) map {i => ID(i + freeNames.size)}
    val canon = new RenameBindings(boundIDs)(τ rename freeIDs)
    (canon, freeInverse,
      (boundIDs, boundNames).zipped.map((k,v) => (k,v))(collection.breakOut))
  }

  def canonizeNames(t : Term): (Term, R, R) = {
    val freeNames = getFreeNames(t)
    val boundNames = (new CollectBindings)(t)
    val freeInverse: Map[Name, Name] =
      ((0 until freeNames.size), freeNames).zipped.map({
        case (i, name) => ID(i) -> name
      })(collection.breakOut)
    val freeIDs = freeInverse map { case (id, name) => name -> χ(id) }
    val boundIDs = (0 until boundNames.size) map {i => ID(i + freeNames.size)}
    val canon = new RenameBindings(boundIDs)(t rename freeIDs)
    (canon, freeInverse,
      (boundIDs, boundNames).zipped.map((k,v) => (k,v))(collection.breakOut))
  }

  implicit class TypeCanonizeNameOps(τ : Type) {
    def canonize = canonizeNames(τ)
  }

  implicit class TermCanonizeNameOps(t : Term) {
    def canonize = canonizeNames(t)
  }

  implicit class MapInversOps[K, V](m: Map[K, V]) {
    def inverse: Map[V, K] = m map (_.swap)
  }
}

trait Substitution extends GlobalRenaming with CanonicalNames {
  def substituteInType(τ : Type, f : Map[Name, Type]): Type = {
    val (canon, invFree, invBound) = τ.canonize
    val freeIDs = invFree.inverse
    val g: Map[Name, Type] = (freeIDs.keySet & f.keySet).map(
      freeName => freeIDs(freeName) -> f(freeName)
    )(collection.breakOut)
    val toAvoid =
      (f map { kv => getFreeNames(kv._2) }).fold(Set.empty)(_ ++ _)
    val invAll = invFree ++ invBound.map({ case (id, boundName) =>
      (id, getFreshName(boundName, toAvoid))
    })
    (canon rename g) renameAll invAll
  }

  def substituteInTerm(t : Term, f : Map[Name, Term]): Term = {
    val (canon, invFree, invBound) = t.canonize
    val freeIDs = invFree.inverse
    val g: Map[Name, Term] = (freeIDs.keySet & f.keySet).map(
      freeName => freeIDs(freeName) -> f(freeName)
    )(collection.breakOut)
    val toAvoid =
      (f map { kv => getFreeNames(kv._2) }).fold(Set.empty)(_ ++ _)
    val invAll = invFree ++ invBound.map({ case (id, boundName) =>
      (id, getFreshName(boundName, toAvoid))
    })
    (canon rename g) renameAll invAll
  }

  implicit class typeSubstitutionOps(τ : Type) {
    def substitute[N <% Name, T <% Type](scheme: (N, T)*): Type =
      substitute(Map(scheme map {kv => (kv._1: Name, kv._2: Type)}: _*))
    def substitute(scheme: Map[Name, Type]): Type =
      substituteInType(τ, scheme)
  }
  implicit class termSubstitutionOps(t : Term) {
    def substitute[N <% Name, T <% Term](scheme: (N, T)*): Term =
      substitute(Map(scheme map {kv => (kv._1: Name, kv._2: Term)}: _*))
    def substitute(scheme: Map[Name, Term]): Term =
      substituteInTerm(t, scheme)
  }
}

trait TypedTerms extends GlobalRenaming {
  case class TypedTerm(canon: Term,
                       Γ    : Map[Name, Type],
                       names: Map[Name, Name]) {
    def getTerm: Term = canon renameAll names

    def getType: Type = (new TypeCheck)(canon)

    class TypeCheck extends TermVisitor[Type] {
      private[this] type T = Type

      def χ(name: Name): T = Γ(name)
      def λ(name: Name, body: T): T = Γ(name) →: body

      def ε(operator: T, operand: T): T = operator match {
        case σ → τ if σ == operand => τ
      }
    }
  }
}

trait Pretty extends TypedTerms {
  trait PrettyVisitor extends Visitor[(String, Int)]
  {
    private type Domain = (String, Int)

    override def ∀(name: Name, body: Domain) =
      template("∀%s. %s", priority_∀, (α(name), 0), (body, 1))

    override def →(σ : Domain, τ : Domain) =
      template("%s → %s", priority_→, (σ, 0), (τ, 1))

    override def ★(f: Domain, x: Domain) =
      template("%s %s", priority_★, (f, 1), (x, 0))

    override def α(name: Name) = (name.toString, priority_∞)
    override def ? = ("?", priority_∞)

    def χ(name: Name): Domain = (name.toString, priority_∞)

    override def λ(name: Name, body: Domain): Domain =
      template("λ%s. %s", priority_λ, (χ(name), 0), (body, 1))

    override def ε(f: Domain, x: Domain) =
      template("%s %s", priority_ε, (f, 1), (x, 0))

    def template(format: String, priority: Int, subs: (Domain, Int)*):
        Domain = {
      val subformats = subs map {
        case ((sub, psub), pmod) => paren(psub, priority + pmod, sub)
      }
      (format.format(subformats: _*), priority)
    }

    def paren(innerPriority: Int, outerPriority: Int, text: String):
        String =
      if (innerPriority > outerPriority)
        text
      else
        "(%s)" format text

    val priority_∀ = 1
    val priority_→ = 5
    val priority_★ = 9

    val priority_λ = 1
    val priority_ε = 9

    val priority_∞ = 0x7FFFFFFF // biggest integer out there
  }

  object PrettyVisitor extends PrettyVisitor

  def pretty(t : Term): String = PrettyVisitor(t)._1
  def pretty(τ : Type): String = PrettyVisitor(τ)._1
  def pretty(t : TypedTerm): String =
    "%s : %s".format(pretty(t.getTerm), pretty(t.getType))
}

trait MinimallyQuantifiedTypes extends Types with FreeNames with Pretty {
  private sealed trait MQ {
    def >>= (f: Set[Name] => MQ): MQ
  }

  private case object NotMQ extends MQ {
    def >>= (f: Set[Name] => MQ): MQ = NotMQ
  }

  private case class Solo(freeNames: Set[Name]) extends MQ {
    def >>= (f: Set[Name] => MQ): MQ = f(freeNames)
  }

  private case class Duo(lhs: Set[Name], rhs: Set[Name]) extends MQ {
    def >>= (f: Set[Name] => MQ): MQ = f(lhs ++ rhs)
  }

  private class IsMinimallyQuantified extends TypeVisitor[MQ] {
    private[this] type T = MQ

    def ∀(name: Name, body: T): T = body match {
      case Duo(lhs, rhs) if (lhs contains name) && (rhs contains name) =>
        Duo(lhs - name, rhs - name)

      case _ =>
        NotMQ
    }

    def →(domain: T, range: T): T =
      domain >>= { domain =>
      range  >>= { range  =>
      Duo(domain, range) }}

    def α(name: Name): T = Solo(Set(name))
    def ? : T            = Solo(Set.empty)

    def ★(typeFun: T, typeArg: T) =
      typeFun >>= { typeFun =>
      typeArg >>= { typeArg =>
      Solo(typeFun ++ typeArg) }}
  }

  implicit class MinimallyQuantifiedTypeOps(τ : Type) {
    def isMinimallyQuantified: Boolean =
      NotMQ != (new IsMinimallyQuantified)(τ)

    def ensureMinimalQuantification: Type =
      if (! isMinimallyQuantified)
        sys error s"Not minimally quantified: ${pretty(τ)}"
      else
        τ
  }
}

object TestMQ extends MinimallyQuantifiedTypes {
/*
  def main(args: Array[String]) {
    val types = List(
      //∀("α", )
    )
  }
 */
}
