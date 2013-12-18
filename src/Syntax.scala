trait Types {
  types =>

  object Type extends NameBindingLanguage {
    override
    def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
      case α_(name)          => α_(name)                // type variable
      case δ_(name)          => δ_(name)                // free type var
      case ∀:(name, body)    => ∀:(name, f(body))       // universal
      case ∃:(name, body)    => ∃:(name, f(body))       // existential
      case →:(domain, range) => →:(f(domain), f(range)) // function type
      case ₌:(functor, arg)  => ₌:(f(functor), f(arg))  // functor app
      case otherwise         => super.fmap(f)(otherwise)
    }
  }

  type Type = Type.ADT

  import Type._

  implicit class InfixTypeConstructors(τ : Type) {
    def →: (σ : Type): → = types.→(σ, τ)
    def ₌  (σ : Type): ₌ = types.₌(τ, σ)
  }

  // free names. δωρεάν όνοματα (?)
  case class δ_[T](name: String) extends Functor[T] {
    def toADT: ADT = δ(name)
  }
  class δ(name: String) extends δ_[ADT](name) with ADT
  object δ {
    def apply(name: String): δ = new δ(name)
    def unapply(freevar: δ): Option[String] = Some(freevar.name)
  }

  case class α_[T](binder: Binder) extends Bound[T] {
    def toADT: ADT = α(binder)
  }
  class α(binder: Binder) extends α_[ADT](binder) with ADT
  object α {
    def apply(binder: Binder): α = new α(binder)
    def unapply(a: α): Option[Binder] = Some(a.binder)
  }

  case class ∀:[T](var binder: Binder, var body: T) extends Functor[T] {
    def toADT: ADT = body match {
      case body: ADT => ∀.replaceBody(binder, body)
    }
  }
  class ∀ extends ∀:[ADT](null, null) with Binder {
    override def toString = s"∀($name, $body)"
  }
  object ∀ extends BinderFactory[∀] {
    def newBinder: ∀ = new ∀
    def bound(binder: Binder): α = α(binder)

    /** universally quantify over a free name */
    def apply(alpha: δ, body: Type): ∀ = ∀(alpha.name) {
      // body of this universal type is procedually generated.
      // nevertheless, it's a valid HOAS because we never examine
      // tvar by folds or pattern matching.
      tvar => body.fold[Type] {
        case δ_(name) if name == alpha.name => tvar
        case otherwise => otherwise.toADT
      }
    }
  }

  case class ∃:[T](var binder: Binder, var body: T) extends Functor[T] {
    def toADT: ADT = body match {
      case body: ADT => ∃.replaceBody(binder, body)
    }
  }
  class ∃ extends ∃:[ADT](null, null) with Binder {
    override def toString = s"∃($name, $body)"
  }
  object ∃ extends BinderFactory[∃] {
    def newBinder: ∃ = new ∃
    def bound(binder: Binder): α = α(binder)
  }

  case class →:[T](domain: T, range: T) extends Functor[T] {
    def toADT: ADT = (domain, range) match {
      case (domain: ADT, range: ADT) => domain →: range
    }
  }
  class →(domain: ADT, range: ADT) extends →:[ADT](domain, range) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($domain, $range)"
  }
  object → {
    def apply(domain: ADT, range: ADT): → = new →(domain, range)
    def unapply(a: →): Option[(ADT, ADT)] = Some((a.domain, a.range))
  }

  case class ₌:[T](functor: T, arg: T) extends Functor[T] {
    def toADT: ADT = (functor, arg) match {
      case (functor: ADT, arg: ADT) => functor ₌ arg
    }
  }
  class ₌(functor: ADT, arg: ADT) extends ₌:[ADT](functor, arg) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($functor, $arg)"
  }
  object ₌ {
    def apply(functor: ADT, arg: ADT): ₌ = new ₌(functor, arg)
    def unapply(a: ₌): Option[(ADT, ADT)] = Some((a.functor, a.arg))
  }
}

trait TypeAbstraction extends Types {
  val Term: NameBindingLanguage
  import Term._

  // type abstraction is not a binder.
  // (making it possible for types to be sub-structures of
  // terms entails too much functor-wrangling.)
  //
  // type abstraction is in a separate trait to avoid the
  // following warning:
  //
  // Class Terms$Λ_ differs only in case from Terms$λ_. Such
  // classes will overwrite one another on case-insensitive
  // filesystems.

  case class Λ_[T](alpha: δ, body: T) extends Functor[T] {
    def toADT: ADT = body match {
      case body: ADT => Λ(alpha, body)
    }
  }
  class Λ(alpha: δ, body: ADT) extends Λ_(alpha, body) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}(${alpha.name}, $body)"
  }
  object Λ {
    def apply(alpha: δ, body: ADT): Λ = new Λ(alpha, body)
    def unapply(tabs: Λ): Option[(δ, ADT)] = Some((tabs.alpha, tabs.body))
  }
}

trait Terms extends TypeAbstraction {
  terms =>

  object Term extends NameBindingLanguage {
    override
    def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
      case χ_(name)        => χ_(name)           // variable
      case λ_(name, body)  => λ_(name, f(body))  // term abstraction
      case Λ_(alpha, body) => Λ_(alpha, f(body)) // type abstraction
      case ₋:(fun, arg)    => ₋:(f(fun), f(arg)) // term application
      case □:(t, σ)        => □:(f(t), σ)        // type application
      case Ξ_(t, σ)        => Ξ_(f(t), σ)        // type amnesia
      case otherwise       => super.fmap(f)(otherwise)
    }
  }

  type Term   = Term.ADT
  type Env[T] = Term.Env[T]

  import Term._

  implicit class InfixTermConstructors(t: Term) {
    def ₋(s: Term): ₋ = terms.₋(t, s)
    def □(σ: Type): □ = terms.□(t, σ)
    def Ξ(σ: Type): Ξ = terms.Ξ(t, σ)
  }

  case class χ_[T](binder: Binder) extends Bound[T] {
    def toADT: ADT = χ(binder)
  }
  class χ(binder: Binder) extends χ_[ADT](binder) with ADT
  object χ {
    def apply(binder: Binder): χ = new χ(binder)
    def unapply(a: χ): Option[Binder] = Some(a.binder)
  }

  case class λ_[T](var binder: Binder, var body: T) extends Functor[T] {
    def toADT: ADT = body match {
      case body: ADT => λ.replaceBody(binder, body)
    }
  }
  class λ extends λ_[ADT](null, null) with Binder {
    override def toString = s"λ($name, $body)"
  }
  object λ extends BinderFactory[λ] {
    def newBinder: λ = new λ
    def bound(binder: Binder): χ = χ(binder)
  }

  case class ₋:[T](fun: T, arg: T) extends Functor[T] {
    def toADT: ADT = (fun, arg) match {
      case (fun: ADT, arg: ADT) => fun ₋ arg
    }
  }
  class ₋(fun: ADT, arg: ADT) extends ₋:[ADT](fun, arg) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($fun, $arg)"
  }
  object ₋ {
    def apply(fun: ADT, arg: ADT): ₋ = new ₋(fun, arg)
    def unapply(a: ₋): Option[(ADT, ADT)] = Some((a.fun, a.arg))
  }

  case class □:[T](t: T, σ: Type) extends Functor[T] {
    def toADT: ADT = t match { case t: ADT => t □ σ }
  }
  class □(t: ADT, σ: Type) extends □:[ADT](t, σ) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($t, $σ)"
  }
  object □ {
    def apply(t: ADT, σ: Type): □ = new □(t, σ)
    def unapply(a: □): Option[(ADT, Type)] = Some((a.t, a.σ))
  }

  case class Ξ_[T](t: T, σ: Type) extends Functor[T] {
    def toADT: ADT = t match { case t: ADT => t Ξ σ }
  }
  class Ξ(t: ADT, σ: Type) extends Ξ_[ADT](t, σ) with ADT {
    override def toString: String =
      s"${getClass.getSimpleName}($t, $σ)"
  }
  object Ξ {
    def apply(t: ADT, σ: Type): Ξ = new Ξ(t, σ)
    def unapply(a: Ξ): Option[(ADT, Type)] = Some((a.t, a.σ))
  }
}
