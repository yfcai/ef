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

    def subst(from: Binder, to: ADT): ADT = subst(Map(from -> to))

    // substitution employs a paramorphism to divert recursion path
    // when the name to be substituted is rebound.
    // paramorphisms are not necessarily compositional.
    // substitution is not.
    def subst(env: Map[Binder, ADT]): ADT = para[ADT] { (before, after) =>
      before match {
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
  }

  object ADT {
    // anamorphism
    def ana[T](psi: Coalgebra[T])(x: T): ADT = (psi(x) map (ana(psi))).toADT
  }

  // NAME BINDING LANGUAGE

  // Binders are names and names are binders.
  //
  // The source of the difficulty of substitution lies in the gap
  // between the lambda term's meaning as a graph and its
  // representation as a tree. We eliminate the difficulty at the
  // root via a graph representation of lambda terms. Objects are
  // nodes. References are edges.
  //
  // This arrangement makes node identity equal to reference
  // identity. Binders are generative: two binders are equal if
  // and only if they occupy the same space on the heap.

  type Env[T] = PartialFunction[Binder, T]

  // a free name has a string
  trait FreeName[T] extends Functor[T] {
    def name: String
  }

  // a bound name has a back edge to its binder
  trait Bound[T] extends Functor[T] {
    def binder: Binder
    override def toString: String = binder.name
  }

  // a binder is a name is a binder
  trait Binder extends ADT {
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

    def reverseTraversal: List[ADT] = this :: body.reverseTraversal

    private[NameBindingLanguage]
    var defaultName: String = "x"

    private def christianMe(body: ADT): String = {
      // - Do you renounce Satan?
      if (body == null)
        // - I do renounce him.
        sys error (s"name of incomplete binder:" +
            s"${getClass.getSimpleName}($defaultName, $body)")
      // - And all his works?
      val usedNames: Set[String] =
        body.traverse.flatMap({
          // - I do renounce them.
          case binder: Binder => Some(binder.name)
          case _ => None
        })(collection.breakOut)
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
