trait NameBindingLanguage {
  // ALGEBRAIC DATA TYPE AS FIXED POINT OF A FUNCTOR

  /** the functor whose fixed point is the algebraic data type */
  trait Functor[T] {
    def map[R](f: T => R) = fmap(f)(this)

    def toADT: ADT
  }

  // algebra and coalgebra defined as usual
  type Algebra  [T] = PartialFunction[Functor[T], T]
  type Coalgebra[T] = PartialFunction[T, Functor[T]]

  // instance Functor f where fmap = ...
  // extension point: adding new data types
  def fmap[T, R](f: T => R): Functor[T] => Functor[R] = {
    case x => sys error s"No clue how to map over $x"
  }

  // one-shot fixed point of a derived functor to support paramorphisms
  case class ParaADT(functor: Functor[(ADT, ParaADT)]) {
    def fold[T](f: (=> ADT, => Functor[T]) => T): T =
      f(functor.map(_._1).toADT, functor map { _._2 fold f})
  }

  // We cheat out of the boilerplates of yet another functor
  // by mutation.
  object ParaADT {
    def apply(adt: ADT): ParaADT = {
      var traversed = adt.traverse
      adt.fold[(ADT, ParaADT)]({
        case functor =>
          val result = (traversed.head, ParaADT(functor))
          traversed = traversed.tail
          result
      })._2
    }
  }

  // fixed point of Functor[T]
  trait ADT extends Functor[ADT] {
    // catamorphism
    def fold[T](f: Algebra[T]): T = f(this map (_ fold f))

    // paramorphism.
    // if a normal function (not a case function) is given as argument,
    // then para does not recurse unless necessary.
    // this is important in avoiding nontermination in the event that
    // the ADT has a cycle.
    def para[T](f: (=> ADT, => Functor[T]) => T): T = ParaADT(this) fold f

    def subst(from: Bound[ADT], to: ADT): ADT = subst(from.binder, to)

    def subst(from: Binder, to: ADT): ADT = subst(Map(from -> to))

    // substitution employs a paramorphism to divert recursion path
    // when the name to be substituted is rebound.
    // paramorphisms are not necessarily compositional.
    // substitution is not.
    def subst(env: Map[Binder, ADT]): ADT = para[ADT] {
      (before, after) => before match {
        case binder: Binder if env isDefinedAt binder =>
          binder subst (env - binder)
        case _ => after match {
          case y: Bound[_] if env.isDefinedAt(y.binder) => env(y.binder)
          case otherwise => otherwise.toADT
        }
      }
    }

    def subst(freeName: FreeName[ADT], replacement: ADT): ADT =
      subst(Map(freeName -> replacement))

    def subst(f: PartialFunction[FreeName[ADT], ADT]): ADT = fold[ADT] {
      case freeName: FreeName[ADT] if f isDefinedAt freeName => f(freeName)
      case otherwise => otherwise.toADT
    }

    /** gives a list of ADTs in postorder */
    def traverse: List[ADT] = reverseTraversal.reverse

    /** list of ADTs in reversed postorder (which is NOT preorder) */
    def reverseTraversal: List[ADT]

    def freeNames: Set[FreeName[ADT]] = reverseTraversal.flatMap({
      case x: FreeName[ADT] => Some(x)
      case _                => None
    })(collection.breakOut)
  }

  object ADT {
    // anamorphism
    def ana[T](psi: Coalgebra[T])(x: T): ADT = (psi(x) map (ana(psi))).toADT
  }

  // CLASSIFICATION OF FUNCTOR CONSTRUCTORS

  trait Π0[T] extends Functor[T]

  trait Π0ADT extends Π0[ADT] with ADT {
    def reverseTraversal = List(this)
  }

  trait Π1[T] extends Functor[T] {
    def π1: T
  }

  trait Π1Binder[T] extends Π1[T] {
    def binder: Binder
    def body: T
    def π1 = body
  }

  trait Π1ADT extends Π1[ADT] with ADT {
    def reverseTraversal: List[ADT] = this :: π1.reverseTraversal
  }

  trait Π2[T] extends Functor[T] {
    def π1: T
    def π2: T
  }

  trait Π2ADT extends Π2[ADT] with ADT {
    def reverseTraversal =
      this :: (π2.reverseTraversal ++ π1.reverseTraversal)
  }

  trait Π2Factory[T <: Π2ADT] {
    def apply(lhs: ADT, rhs: ADT): T
    def unapply(a: T): Option[(ADT, ADT)] = Some((a.π1, a.π2))
  }

  // NAME BINDING LANGUAGE

  type Env[T] = PartialFunction[Binder, T]

  // a free name has a string
  trait FreeName[T] extends Π0[T] {
    def name: String
  }

  trait FreeNameFactory[T <: FreeName[ADT]] {
    def apply(name: String): T
    def unapply(freevar: T): Option[String] = Some(freevar.name)

    def avoid(usedNames: Set[String]): T = {
      val startingID = 0
      var i = startingID
      while (usedNames contains i.toString) i += 1
      apply(i.toString)
    }

    def avoid(things: ADT*): T =
      avoid(things.map(_.freeNames.map(_.name)).
                   fold(Set.empty[String])(_ ++ _))
  }

  // a bound name has a back edge to its binder
  trait Bound[T] extends Π0[T] {
    def binder: Binder
    override def toString: String = binder.name
  }

  // a binder is a name is a binder
  trait Binder extends Π1Binder[ADT] with Π1ADT {
    // inherited from case class of the functor.
    // they should be mutated nowhere outside trait NameBindingLanguage
    // but we can't make them private because the case classes has to
    // "okay" their mutability.
    var binder: Binder
    var body: ADT

    // cleverly loop to self
    binder = this

    lazy val name: String = christianMe(body)

    // convert a binder to HOAS.
    // one can also convert an HOAS to a binder: see BinderFactory.apply
    def apply(arg: ADT): ADT = (toFun[ADT] { case x => x.toADT })(arg)

    def toFun[T](algebra: Algebra[T]): T => T = x => body.fold[T] {
      case y: Bound[_] if y.binder == this => x
      case otherwise => algebra(otherwise)
    }

    private[NameBindingLanguage]
    var defaultName: String = "x"

    private def christianMe(body: ADT): String = {
      // - Do you renounce Satan?
      if (body == null)
        // - I do renounce him.
        sys error (s"name of incomplete binder:" +
            s"${getClass.getSimpleName}($defaultName, $body)")
      // - And all his works?
      //   (which consists of binders above anything bound by you)
      //   (assume that all case classes extend one of the Πn traits)
      val usedNames = body.fold[Option[Set[String]]]({
        case x: Bound[_] if x.binder == this =>
          Some(Set.empty)
        // - I do renounce them.
        case b: Π1Binder[Option[Set[String]]] if b.body != None =>
          Some(b.body.get + b.binder.name)
        case p: Π1[_] =>
          p.π1
        case p: Π2[_] => (p.π1, p.π2) match {
          case (None, None) => None
          case (None, some) => some
          case (some, None) => some
          case (Some(x), Some(y)) => Some(x ++ y)
        }
        case _: Π0[_] =>
          None
      }).fold(Set.empty[String])(identity)
      var myName = defaultName
      var startingIndex = -1
      var i = startingIndex
      // - And all his pomps?
      while (usedNames contains myName) {
        i = i + 1
        // - I do renounce them.
        if (i == startingIndex)
          sys error "oops, I've renounced everything."
        myName = defaultName + i
        // - Will you be baptized?
      }
      // - I will.
      // - In nomine Patri, et Filii, et Spiritus Sancti,
      //   Michael Rizzi, go in peace.
      myName
      // (this is an excerpt from Godfather :) )
    }

    // binders are generative. no two binders are alike.

    override val hashCode: Int = Binder.nextHashCode

    override def equals(other: Any): Boolean = other match {
      case other: Binder => other eq this // s.t. other: AnyRef
      case _ => false
    }

    override def toString: String =
      s"${getClass.getSimpleName}($name, $body)"

    def detachNestedDoppelgaenger: (List[Binder], ADT) = body match {
      case b: Binder if b.getClass == this.getClass =>
        val (tail, body) = b.detachNestedDoppelgaenger
        (this :: tail, body)
      case body =>
        (List(this), body)
    }
  }

  object Binder {
    private[NameBindingLanguage]
    var thisHashCode: Int = -1

    def nextHashCode(): Int = {
      thisHashCode += 1
      thisHashCode
    }
  }

  trait BinderFactory[T <: Binder] {
    def newBinder(): T
    def bound(binder: T): ADT with Bound[ADT]

    // constructs a binder from an HOAS, passing itself as the argument

    def apply(body: ADT => ADT): T = {
      val binder = newBinder
      binder.body = body(bound(binder))
      binder
    }

    def apply(defaultName: String)(body: ADT => ADT): T = {
      val binder = newBinder
      binder.defaultName = defaultName
      binder.body = body(bound(binder))
      binder
    }

    def apply(namesToBind: Seq[FreeName[ADT]], body: ADT): T =
      ((namesToBind foldRight body) {
        case (free, body) => apply(free.name) { x => body.subst(free, x) }
      }).asInstanceOf[T]

    def apply(xs: FreeName[ADT]*)(body: => ADT): T =
      apply(xs, body)

    def unapply(b: T): Option[(Binder, ADT)] = Some((b.binder, b.body))

    def replaceBody(binder: Binder, body: ADT): Binder =
      apply(binder.defaultName) { x => body.subst(binder, x) }
  }
}
