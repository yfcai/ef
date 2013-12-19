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

  type Type           = Type.ADT
  type TypeFunctor[X] = Type.Functor[X]

  import Type._

  implicit class InfixTypeConstructorsAndUsefulOps(τ : Type) {
    def →: (σ : Type): → = types.→(σ, τ)
    def ₌  (σ : Type): ₌ = types.₌(τ, σ)

    def argumentTypes: Iterator[Type] = new Iterator[Type] {
      var currentType = τ
      def hasNext = currentType.isInstanceOf[→]
      def next = currentType match {
        case domain → range =>
          currentType = range
          domain
      }
    }
  }

  // free names. δωρεάν όνοματα (?)
  case class δ_[T](name: String) extends FreeName[T] {
    def toADT: ADT = δ(name)
  }
  class δ(name: String) extends δ_[ADT](name) with Π0ADT {
    override def toString = s"δ($name)"
  }
  object δ extends FreeNameFactory[δ] {
    def apply(name: String): δ = new δ(name)
  }

  case class α_[T](binder: Binder) extends Bound[T] {
    def toADT: ADT = α(binder)
  }
  class α(binder: Binder) extends α_[ADT](binder) with Π0ADT
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
    def bound(binder: ∀): α = α(binder)
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
    def bound(binder: ∃): α = α(binder)
  }

  case class →:[T](domain: T, range: T) extends Functor[T] {
    def toADT: ADT = (domain, range) match {
      case (domain: ADT, range: ADT) => domain →: range
    }
  }
  class →(domain: ADT, range: ADT) extends →:[ADT](domain, range) with Π2ADT {
    override def toString = s"→($domain, $range)"
    def π1 = domain
    def π2 = range
  }
  object → extends Π2Factory[→] {
    def apply(domain: ADT, range: ADT): → = new →(domain, range)
  }

  case class ₌:[T](functor: T, arg: T) extends Functor[T] {
    def toADT: ADT = (functor, arg) match {
      case (functor: ADT, arg: ADT) => functor ₌ arg
    }
  }
  class ₌(functor: ADT, arg: ADT) extends ₌:[ADT](functor, arg) with Π2ADT {
    override def toString = s"₌($functor, $arg)"
    def π1 = functor
    def π2 = arg
  }
  object ₌ extends Π2Factory[₌] {
    def apply(functor: ADT, arg: ADT): ₌ = new ₌(functor, arg)
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

  case class Λ_[T](alpha: δ, body: T) extends Π1[T] {
    def toADT: ADT = body match {
      case body: ADT => Λ(alpha, body)
    }
    def π1 = body
  }
  class Λ(alpha: δ, body: ADT) extends Λ_(alpha, body) with Π1ADT {
    override def toString = s"Λ(${alpha.name}, $body)"

    def detachNestedDoppelgaenger: (List[Λ], ADT) = body match {
      case tabs: Λ =>
        val (tail, body) = tabs.detachNestedDoppelgaenger
        (this :: tail, body)
      case _ =>
        (List(this), body)
    }
  }
  object Λ {
    def apply(alpha: δ, body: ADT): Λ = new Λ(alpha, body)
    def unapply(tabs: Λ): Option[(δ, ADT)] = Some((tabs.alpha, tabs.body))

    def apply(alphas: Seq[δ], body: ADT): ADT =
      (alphas foldRight body) { case (alpha, body) => apply(alpha, body) }
  }

  // likewise about Ξ, ξ
  case class Ξ_[T](t: T, σ: Type) extends Π1[T] {
    def toADT: ADT = t match { case t: ADT => Ξ(t, σ) }
    def π1 = t
  }
  class Ξ(t: ADT, σ: Type) extends Ξ_[ADT](t, σ) with Π1ADT {
    override def toString = s"Ξ($t, $σ)"
  }
  object Ξ {
    def apply(t: ADT, σ: Type): Ξ = new Ξ(t, σ)
    def unapply(a: Ξ): Option[(ADT, Type)] = Some((a.t, a.σ))
  }
}

trait Terms extends TypeAbstraction {
  terms =>

  object Term extends NameBindingLanguage {
    override
    def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
      case χ_(name)        => χ_(name)           // variable
      case ξ_(name)        => ξ_(name)           // free variable
      case λ_(name, body)  => λ_(name, f(body))  // term abstraction
      case Λ_(alpha, body) => Λ_(alpha, f(body)) // type abstraction
      case ₋:(fun, arg)    => ₋:(f(fun), f(arg)) // term application
      case □:(t, σ)        => □:(f(t), σ)        // type application
      case Ξ_(t, σ)        => Ξ_(f(t), σ)        // type amnesia
      case otherwise       => super.fmap(f)(otherwise)
    }
  }

  type Term           = Term.ADT
  type TermFunctor[X] = Term.Functor[X]

  import Term._

  implicit class InfixTermConstructorsAndUsefulOps(t: Term) {
    def ₋(s: Term): ₋ = terms.₋(t, s)
    def □(σ: Type): □ = terms.□(t, σ)
    def Ξ(σ: Type): Ξ = terms.Ξ(t, σ)
  }

  case class χ_[T](binder: λ) extends Bound[T] {
    def toADT: ADT = χ(binder)
  }
  class χ(binder: λ) extends χ_[ADT](binder) with Π0ADT
  object χ {
    def apply(binder: λ): χ = new χ(binder)
    def unapply(a: χ): Option[λ] = Some(a.binder)
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
    def bound(binder: λ): χ = χ(binder)
  }

  case class ₋:[T](fun: T, arg: T) extends Π2[T] {
    def toADT: ADT = (fun, arg) match {
      case (fun: ADT, arg: ADT) => fun ₋ arg
    }
    def π1 = fun
    def π2 = arg
  }
  class ₋(fun: ADT, arg: ADT) extends ₋:[ADT](fun, arg) with Π2ADT {
    override def toString = s"₋($fun, $arg)"
  }
  object ₋ extends Π2Factory[₋] {
    def apply(fun: ADT, arg: ADT): ₋ = new ₋(fun, arg)
  }

  case class □:[T](t: T, σ: Type) extends Π1[T] {
    def toADT: ADT = t match { case t: ADT => t □ σ }
    def π1 = t
  }
  class □(t: ADT, σ: Type) extends □:[ADT](t, σ) with Π1ADT {
    override def toString = s"□($t, $σ)"
  }
  object □ {
    def apply(t: ADT, σ: Type): □ = new □(t, σ)
    def unapply(a: □): Option[(ADT, Type)] = Some((a.t, a.σ))
  }

  // free variables
  case class ξ_[T](name: String) extends FreeName[T] {
    def toADT: ADT = ξ(name)
  }
  class ξ(name: String) extends ξ_[ADT](name) with Π0ADT {
    override def toString = s"ξ($name)"
  }
  object ξ extends FreeNameFactory[ξ] {
    def apply(name: String): ξ = new ξ(name)
  }

  trait ExtractLambdas {
    // extract lambdas in reverse preorder
    def extractLambdas(term: Term): List[λ] =
      term.reverseTraversal.flatMap[λ, List[λ]] {
        case abs: λ => Some(abs)
        case _      => None
      }
  }

  // terms with argument types annotated
  case class ChurchTerm(term: Term, annotations: Map[λ, Type])
  extends ExtractLambdas
  {
    def from(subterm: Term) = ChurchTerm(subterm, annotations)

    def subst(β: δ, τ: Type): ChurchTerm =
      subst(Map(β -> τ): PartialFunction[Type.FreeName[Type], Type])

    def subst(f: PartialFunction[Type.FreeName[Type], Type]): ChurchTerm =
      ChurchTerm(term,
        annotations map { case (abs, τ) => (abs, τ subst f) })

    // all used type variable names regardless of their nature
    def freeTypeNames: Set[String] = annotations.flatMap({
      case (abs, τ) => τ.freeNames.map(_.name)
    })(collection.breakOut)

    def toProto: ProtoChurchTerm =
      ProtoChurchTerm(term, extractLambdas(term) map annotations)
  }

  /** Church terms in a state of incompleteness */
  case class ProtoChurchTerm(term: Term, annotations: List[Type])
  extends ExtractLambdas
  {
    /** the Church term instrumentality project */
    def toChurchTerm: ChurchTerm =
      ChurchTerm(term,
        (annotations, extractLambdas(term)).zipped.map({
          case (τ, abs) => (abs, τ)
        })(collection.breakOut))

    def updateTerm(newTerm: Term) = ProtoChurchTerm(newTerm, annotations)
  }
}

trait Modules extends Terms {
  object Module {
    def empty = Module(Map.empty, Map.empty, Map.empty)
  }

  case class Module(
    synonyms   : Map[δ, Type],
    signatures : Map[ξ, Type],
    definitions: Map[ξ, ChurchTerm])
  {
    def addSynonym(a: δ, τ: Type): Module = {
      if (synonyms contains a)
        sys error s"\nrepeated synonym:\ntype $a = $τ"
      Module(synonyms updated (a, τ), signatures, definitions)
    }

    def addSignature(x: ξ, τ: Type): Module = {
      if (signatures contains x)
        sys error s"\nrepeated signature:\n$x : $τ"
      Module(synonyms, signatures updated (x, τ), definitions)
    }

    def addDefinition(x: ξ, xdef: ChurchTerm): Module = {
      if (definitions contains x)
        sys error s"\nrepeated definition:\n$x = $xdef"
      Module(synonyms, signatures, definitions updated (x, xdef))
    }

    def Γ(x: ξ): Type = signatures(x) // override this for literals
  }

  // a subclass of module supporting literals perhaps?
}

// α-equivalence, pretty printer (unparse)
trait Syntax extends Modules with ASTConversions {
  implicit class unparsingTypes(τ: Type) {
    def unparse: String = τ.toAST.unparse

    def α_equiv(σ: Type): Boolean = (σ, τ) match {
      case (α(binder_σ), α(binder_τ)) =>
        binder_σ == binder_τ
      case (δ(name_σ), δ(name_τ)) =>
        name_σ == name_τ
      case (σ: ∀, τ: ∀) =>
        val newName = δ.avoid(σ, τ)
        σ(newName) α_equiv τ(newName)
      case (σ: ∃, τ: ∃) =>
        val newName = δ.avoid(σ, τ)
        σ(newName) α_equiv τ(newName)
      case (σ0 → σ1, τ0 → τ1) =>
        (σ0 α_equiv τ0) && (σ1 α_equiv τ1)
      case (σ0 ₌ σ1, τ0 ₌ τ1) =>
        (σ0 α_equiv τ0) && (σ1 α_equiv τ1)
      case _ =>
        false
    }
  }

  implicit class unparsingTerms(t: ChurchTerm) {
    def unparse: String = t.toAST.unparse

    def α_equiv(s: ChurchTerm): Boolean = (s.term, t.term) match {
      case (χ(binder_s), χ(binder_t)) =>
        binder_s == binder_t
      case (ξ(name_s), ξ(name_t)) =>
        name_s == name_t
      case (abs_s: λ, abs_t: λ) =>
        val x = ξ.avoid(abs_s, abs_t)
        (s from abs_s.body).toProto.updateTerm(abs_s(x)).toChurchTerm α_equiv
        (t from abs_t.body).toProto.updateTerm(abs_t(x)).toChurchTerm
      // here, the interference between two functors become apparent.
      // the name binding cabability of one is no help to the other.
      case (Λ(β, body_s), Λ(γ, body_t)) =>
        val ε = δ.avoid(s.freeTypeNames ++ t.freeTypeNames)
        s.from(body_s).subst(β, ε) α_equiv t.from(body_t).subst(γ, ε)
      case ((fs ₋ xs), (ft ₋ xt)) =>
        ((s from fs) α_equiv (t from ft)) &&
        ((s from xs) α_equiv (t from xt))
      case ((xs □ σ), (xt □ τ)) =>
        (σ α_equiv τ) && ((s from xs) α_equiv (t from xt))
      case ((xs Ξ σ), (xt Ξ τ)) =>
        (σ α_equiv τ) && ((s from xs) α_equiv (t from xt))
      case _ =>
        false
    }
  }

  implicit class unparsingModules(module: Module) {
    def unparse: String = {
      val synonyms = module.synonyms.toList.sorted(byName1[Type]) map {
        case (β, τ) =>
          s"type ${β.name} = ${τ.unparse}"
      }
      val bodied = for {
        (f, τ) <- module.signatures.toList.sorted(byName2[Type])
        sig  = s"${f.name} : ${τ.unparse}"
        impl = if (module.definitions contains f)
                 s"\n${f.name} = ${module.definitions(f).unparse}"
               else ""

      } yield sig + impl
      val nohead = for {
        (f, body) <- (for {
          (f, body) <- module.definitions
          if ! (module.signatures contains f)
        } yield (f, body)).toList.sorted(byName2[Object])
      } yield s"${f.name} = ${body.unparse}"
      (synonyms ++ bodied ++ nohead) mkString "\n\n"
    }

    private[this]
    implicit def byName1[T](implicit c: Ordering[String]) =
      new Ordering[(δ, T)] {
        def compare(x: (δ, T), y: (δ, T)): Int =
          c.compare(x._1.name, y._1.name)
      }

    private[this]
    implicit def byName2[T](implicit c: Ordering[String]) =
      new Ordering[(ξ, T)] {
        def compare(x: (ξ, T), y: (ξ, T)): Int =
          c.compare(x._1.name, y._1.name)
      }
  }
}
