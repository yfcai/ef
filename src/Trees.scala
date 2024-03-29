import scala.language.implicitConversions

trait Trees extends Names {
  trait Genus // type, terms, etc

  trait Tag {
    def genus: Genus

    // subgenera is optional. if tree is variadic, no subgenera
    // makes sense.
    def subgenera: Option[Seq[Genus]] = None

    val _subgenera = subgenera

    // extension point: pretty printer
    def unparse(t: Tree): String = t.print
  }

  // tag for variadic untyped trees
  trait UnclassifiedTag extends Tag with Genus { def genus = this }

  case class InappropriatePrison(want: Tag, has: Tag) extends Exception

  trait TreeF[T] {
    def tag: Tag
    def children: Seq[T]

    def map[S](f: T => S): TreeF[S] = this match {
      case ∙:(tag, get) => ∙:(tag, get)
      case ⊹:(tag, children @ _*) =>
        ⊹:(tag,
          // for performance, systematically rewrite maps into folds
          // children map f
          children.foldRight[List[S]](Nil)((x, acc) => f(x) :: acc)
              : _*)
    }

    // unsafe
    def as[R]: R = this match {
      case ∙:(_, get) => get.asInstanceOf[R]
    }
  }
  case class ∙:[T, S](tag: LeafTag, get: S) extends TreeF[T] {
    def children = Nil
  }
  case class ⊹:[T](tag: Tag, children: T*) extends TreeF[T]

  trait LeafTag extends Tag {
    def man: Manifest[_]
    override final def subgenera = Some(Nil)
  }

  trait KnownLeafTag[T] extends LeafTag {
    def man: Manifest[T]
    def get(t: Tree): T = t match {
      case node @ ∙(tag, _) if tag == this => node.as[T]
    }
  }

  trait FreeName extends KnownLeafTag[String]
  { def man = manifest[String] }
  trait DeBruijn extends KnownLeafTag[Int]
  { def man = manifest[Int] }

  trait Binder extends Tag {
    def prison        : DeBruijn // I am not a number...
    def freeName      : FreeName // I am a free variable.
    def genus         : Genus
    def extraSubgenera: Seq[Genus] = Nil
    // in subclasses, extraSubgenera should always be a "def", not "val",
    // to avoid NullPointerException during initialization

    if (prison.genus != freeName.genus)
      sys error s"""|binder $this changes prisoners' identity from
        |${freeName.genus} to ${prison.genus}
        |""".stripMargin

    override def subgenera =
      Some(§.genus +: (extraSubgenera :+ genus))

    def        bodyOf(t: Tree): Tree   = t.children.last
    def defaultNameOf(t: Tree): String = t.children.head.as[String]
    def annotationsOf(t: Tree): Seq[Tree] = t.children.tail.init

    def bindingGenus: Genus = prison.genus

    // bind a free name
    def bind(x: String, trees: Tree*): Tree =
      try {
        val (annotations, b) = trees.splitAt(trees.length - 1)
        ⊹(this, §(x) +: (annotations :+ b.head.imprison(prison, x, 0)): _*)
      }
      catch {
        case e: InappropriatePrison =>
          sys error s"$this can't bind $x in ${trees.last}"
      }

    // free a bound number
    def unbind(t: Tree): Option[(∙[String], Seq[Tree])] =
      unbind(t, Set.empty)

    def unbind(t: Tree, toAvoid: Set[String]):
        Option[(∙[String], Seq[Tree])] =
      t match {
        case ⊹(tag, _*) if tag == this =>
          val x = free(nameOf(t, toAvoid))
          Some((x, annotationsOf(t) :+ t(x)))
        case _ =>
          None
      }

    // bind list of names
    // sadly, due to erasure, we can't offer an overloaded version
    // acting on list of names for annotation-free binders.
    def binds(xs: Seq[String], body: Tree): Tree =
      bindAll(xs map (x => (x, Nil)), body)

    def bindAll(xs: Seq[(String, Seq[Tree])], body: Tree): Tree =
      if (xs.isEmpty)
        body
      else {
        val (x, notes) = xs.head
        bind(x, notes :+ bindAll(xs.tail, body): _*)
      }

    // unbind until impossible, coming up with list of distinct names
    def unbindAll(t: Tree): (List[(String, Seq[Tree])], Tree) =
      unbindAll(t, Set.empty)

    def unbindAll(t: Tree, toAvoid: Set[String]):
        (List[(String, Seq[Tree])], Tree) =
      unbind(t, toAvoid) match {
        case Some((x, body)) =>
          // no need to add x.get. it's already there in "nameOf".
          val (xs, realBody) = unbindAll(body.last, toAvoid)
          ((x.get, body.init) :: xs, realBody)
        case None =>
          (Nil, t)
      }

    // count the number of bound occurrences in this tree
    def count(t: Tree): Int = { val x = free(nameOf(t)) ; t(x) count x }

    def free(x: String): ∙[String] = ∙(freeName, x)

    def imprison(x: String, body: Tree): Tree =
      body.imprison(prison, x, 0)

    // name discovery in a namespace
    def nameOf(t: Tree): String = t.shadowlessName match {
      case Some(name) =>
        name
      case None =>
        val name = nameOf(t, Set.empty)
        t.shadowlessName = Some(name)
        name
    }

    def nameOf(t: Tree, _toAvoid: Set[String]): String =
      Subscript.newName(
        defaultNameOf(t),
        _toAvoid ++ t.freeNames ++
          crossedNames(bodyOf(t), 0).fold(Set.empty[String])(identity))

    // names of binders crossing a back-reference path
    // with the same prison
    def crossedNames(t: Tree, i: Int): Option[Set[String]] =
      if (i == 0) {
        t.crossedNames0 match {
          case Some(names) =>
            names
          case None =>
            val names = computeCrossedNames(t, i)
            t.crossedNames0 = Some(names)
            names
        }
      }
      else
        computeCrossedNames(t, i)

    def computeCrossedNames(t: Tree, i: Int): Option[Set[String]] =
      t match {
        case ⊹(tag: Binder, children @ _*) =>
          collectOptions(
            // would write:
            //
            //   children.map(x => computeCrossedNames(x, i + 1))
            //
            // have to write the following to save 1 sec on lists
            // because `sizeHint` is a hotspot (lol)
            children.foldRight[List[Option[Set[String]]]](Nil) {
              case (x, acc) =>
                computeCrossedNames(x, i + 1) :: acc
            }
          ).
            map { x =>
              if (tag.prison == this.prison) // name-spacing
                x + tag.nameOf(t)
              else
                x
            }
        case ⊹(tag, children @ _*) =>
          collectOptions(
            // children map (x => computeCrossedNames(x, i))
            children.foldRight[List[Option[Set[String]]]](Nil) {
              case (x, acc) =>
                computeCrossedNames(x, i) :: acc
            })
        case ∙(tag: DeBruijn, j) if j == i =>
          Some(Set.empty[String])
        case _ =>
          None
      }

    // spec of collectOptions
    // we write an optimized version below
    // def collectOptions[S](x: Seq[Option[S]])(op: (S, S) => S): Option[S] = {
    //   val existing = x withFilter (_ != None) map (_.get)
    //   if (existing.isEmpty)
    //     None
    //   else
    //     Some(existing.tail.fold(existing.head)(op))
    // }
    def collectOptions(x: Seq[Option[Set[String]]]):
        Option[Set[String]] = {
      var hasSome: Boolean = false
      val builder = Set.newBuilder[String]
      x.withFilter(_ != None).foreach { opt =>
        hasSome = true
        builder ++= opt.get
      }
      if (hasSome)
        Some(builder.result)
      else
        None
    }
  }


  // branches and leafs, worthy of boilerplates
  class ∙[S: Manifest](tag: LeafTag, get: S)
      extends ∙:[Tree, S](tag, get) with Tree {
    if (tag.man != manifest[S])
      sys error s"""|incongruent manifests in leaves.
        |declared: ${tag.man}
        |actual  : ${manifest[S]}
        |in
        |$this
        |""".stripMargin
    override def toString = s"∙($tag, $get)"

    def computeFreeNames: Set[String] =
      if (tag.isInstanceOf[FreeName])
        Set(get.asInstanceOf[String])
      else
        Set.empty[String]
  }
  class ⊹(tag: Tag, children: Tree*)
      extends ⊹:[Tree](tag, children: _*) with Tree {
    override def toString =
      s"⊹($tag, ${children.map(_.toString).mkString(", ")})"

    def computeFreeNames: Set[String] = {
      val builder = Set.newBuilder[String]
      children.foreach (builder ++= _.freeNames)
      builder.result
    }
  }

  object ∙ {
    def apply[S: Manifest](tag: LeafTag, get: S): ∙[S] = new ∙(tag, get)
    def unapply[S](x: ∙[S]): Option[(LeafTag, S)] = Some((x.tag, x.get))
  }
  object ⊹ {
    def apply(tag: Tag, children: Tree*): ⊹ = new ⊹(tag, children: _*)
    def unapplySeq(y: ⊹): Option[(Tag, Seq[Tree])] =
      Some((y.tag, y.children))
  }

  object Tree extends (TreeF[Tree] => Tree) {
    def apply(x: TreeF[Tree]): Tree = x match {
      case ∙:(tag, get) => new ∙(tag, get)(tag.man.asInstanceOf[Manifest[Any]])
      case ⊹:(tag, children @ _*) => ⊹(tag, children: _*)
    }
  }

  case class BinderSpec(tag: Binder, x: String, annotations: Tree*) {
    def annotation: Tree = annotations match {
      case Seq(note) => note
    }
  }

  trait Tree extends TreeF[Tree] {
    // dynamic type safety, disabled for performance
    //
    // if (tag._subgenera != None &&
    //     children.map(_.tag.genus) != tag._subgenera.get)
    //   sys error s"""|subgenera mismatch
    //     |${tag.subgenera.get.toString}
    //     |${this.print}
    //     |""".stripMargin

    def fold[S](f: TreeF[S] => S): S = f(this map (_ fold f))

    // substitution of variable bound here
    // (only works on binders)
    def apply(xdef: Tree): Tree = tag match {
      case tag: Binder =>
        require(tag.bindingGenus == xdef.tag.genus)
        (tag bodyOf this subst (0, xdef.shift(1, 0))).
          shift(-1, 1)
      case _ =>
        sys error s"expect binder, got: ${this.print}"
    }

    // substitution of bound variable
    def subst(i: Int, xdef: Tree): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag,
          //children map (_.subst(i + 1, xdef))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.subst(i + 1, xdef) :: acc
          }
              : _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag,
          //children map (_.subst(i, xdef))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.subst(i, xdef) :: acc
          }
              : _*)
      case ∙(tag: DeBruijn, j: Int) if i == j =>
        require(xdef.tag.genus == tag.genus)
        xdef.shift(i, 0)
      case otherwise =>
        otherwise
    }

    // substitution of free variable
    def subst(x: ∙[String], xdef: Tree): Tree = this match {
      case ∙(tag, get) if x.tag == tag && x.get == get =>
        xdef
      case x @ ∙(_, _) =>
        x
      case ⊹(binder: Binder, children @ _*) =>
        val newDef = xdef.shift(1, 0)
        ⊹(binder,
          //children.map(_.subst(x, newDef))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.subst(x, newDef) :: acc
          }
              : _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag,
          //children.map(_.subst(x, xdef))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.subst(x, xdef) :: acc
          }
              : _*)
    }

    // substitute all free variables of identical genus
    // can't handle binders because "fold" is evil......
    def subst(x: String, xdef: Tree): Tree = fold[Tree] {
      case ∙:(tag, get) if tag.genus == this.tag.genus && x == get =>
        xdef
      case ⊹:(binder: Binder, children @ _*) =>
        sys error s"unhandled. beware shifts."
      case otherwise => Tree(otherwise)
    }

    // parallel substitituion of all free variables of matching genus
    def subst(parallel: Map[String, Tree]): Tree = fold[Tree] {
      case ∙:(tag: FreeName, x: String) if parallel.contains(x) =>
        val xdef = parallel(x)
        require(tag.genus == xdef.tag.genus)
        xdef
      case otherwise => Tree(otherwise)
    }

    // put a free variable in prison, give it numbers
    def imprison(prison: DeBruijn, x: String, i: Int): Tree =
      this match {
        case ⊹(tag: Binder, children @ _*) =>
          ⊹(tag,
            //children map (_.imprison(prison, x, i + 1))
            children.foldRight[List[Tree]](Nil) { (s, acc) =>
              s.imprison(prison, x, i + 1) :: acc
            }
                : _*)
        case ⊹(tag, children @ _*) =>
          ⊹(tag,
            //children map (_.imprison(prison, x, i))
            children.foldRight[List[Tree]](Nil) { (s, acc) =>
              s.imprison(prison, x, i) :: acc
            }
                : _*)
        case ∙(tag: FreeName, get) if get == x =>
          if (tag.genus != prison.genus)
            throw InappropriatePrison(prison, tag)
          ∙(prison, i)
        case otherwise =>
          otherwise
      }

    // d-place shift of this above cutoff c
    def shift(d: Int, c: Int): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag,
          //children map (_.shift(d, c + 1))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.shift(d, c + 1) :: acc
          }
              : _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag,
          //children map (_.shift(d, c))
          children.foldRight[List[Tree]](Nil) { (s, acc) =>
            s.shift(d, c) :: acc
          }
              : _*)
      case ∙(tag: DeBruijn, j: Int) if j >= c =>
        ∙(tag, j + d)
      case otherwise =>
        otherwise
    }

    def unparse: String = tag unparse this

    def print: String = print(0, 2)

    def print(indent: Int, increment: Int): String =
      lines(indent, increment, Nil) mkString "\n"

    // primitive tree-like printing
    def lines(indent: Int, increment: Int, env: Seq[String]):
        Seq[String] = {
      def put(x: Any): String = s"${Array.fill(indent)(' ').mkString}$x"
      this match {
        case ⊹(tag: Binder, children @ _*) =>
          val name = tag nameOf this
          s"${put(tag)}, binder of $name" +: (children flatMap {
            _.lines(indent + increment, increment, name +: env)
          })

        case ⊹(tag, children @ _*) =>
          put(tag) +: (children flatMap {
            _.lines(indent + increment, increment, env)
          })

        case ∙(tag: DeBruijn, j: Int) =>
          if (j >= env.length)
            Seq(this.toString)
          else
            Seq(s"${put(tag)}, bound of ${env(j)}")

        case _ =>
          Seq(put(this))
      }
    }

    // collect all free names
    lazy val freeNames: Set[String] = computeFreeNames

    def computeFreeNames: Set[String]

    // traversals

    def preorder: Iterator[Tree] = this match {
      case ∙(_, _) => Iterator(this)
      case ⊹(_, children @ _*) => Iterator(this) ++
        children.flatMap(_.preorder) // ++ is call-by-name for iterators
    }

    def blindPreorder: Iterator[(Tree, Map[String, Tree])] =
      blindPreorder2.map(t => (t._1, t._2))

    def blindPreorder2: Iterator[(Tree, Map[String, Tree], Set[String])] = {
      def loop(t: Tree, gamma: Map[String, Tree], delta: Set[String]):
          Iterator[(Tree, Map[String, Tree], Set[String])] = t match {
        case ∙(_, _) =>
          Iterator((t, gamma, delta))
        // this is λ before λ is declared.
        case ⊹(binder: Binder, _name, _note, _body)
            if binder.genus == this.tag.genus =>
          binder.unbind(t).get match {
            case (x, Seq(note, body)) =>
              val newGamma = gamma.updated(x.get, note)
              Iterator((t, gamma, delta)) ++
              loop(x, newGamma, delta) ++
              loop(note, gamma, delta) ++
              loop(body, newGamma, delta)
          }
        // this is Λ before Λ is declared.
        case ⊹(binder: Binder, _, _)
            if binder.genus == this.tag.genus =>
          binder.unbind(t).get match {
            case (x, bodies) =>
              val newDelta = delta + x.get
              Iterator((t, gamma, delta)) ++
              loop(x, gamma, newDelta) ++
              bodies.flatMap(s => loop(s, gamma, newDelta))
          }
        case ⊹(_, children @ _*) =>
          Iterator((t, gamma, delta)) ++
          children.flatMap(s => loop(s, gamma, delta))
      }
      loop(this, Map.empty, Set.empty)
    }

    // count number of occurrences of something
    def count(x: Tree): Int = count(_ == x)
    def count(f: Tree => Boolean): Int = preorder.count(f)

    // α-equivalence
    def α_equiv (that: Tree): Boolean = (this, that) match {
      case (⊹(tag1: Binder, sub1 @ _*), ⊹(tag2: Binder, sub2 @ _*)) =>
        tag1 == tag2 &&
          // not comparing default names on purpose
          None == (sub1.tail, sub2.tail).zipped.find({
            case (lhs, rhs) => ! (lhs α_equiv rhs)
          })
      case (⊹(tag1, sub1 @ _*), ⊹(tag2, sub2 @ _*)) =>
        tag1 == tag2 &&
          None == (sub1, sub2).zipped.find({
            case (lhs, rhs) => ! (lhs α_equiv rhs)
          })
      case _ => this == that
    }

    // interactions with binders

    // to be bound by lots of binders
    def boundBy(xs: Seq[BinderSpec]): Tree =
      xs.foldRight(this) {
        case (BinderSpec(binder, x, notes @ _*), body) =>
          binder.bind(x, notes :+ body: _*)
      }

    // unbind lots of binders
    def unbindAll(ofWhom: Binder*):
        (List[BinderSpec], Tree) =
      unbindAll(Set.empty[String], ofWhom: _*)

    def unbindAll(toAvoid: Set[String], ofWhom: Binder*):
        (List[BinderSpec], Tree) =
      unbindAll(toAvoid, ofWhom contains _)

    def unbindAll(toAvoid: Set[String], predicate: Binder => Boolean):
        (List[BinderSpec], Tree) =
      this match {
        case ⊹(tag: Binder, children @ _*) if predicate(tag) =>
          val (prefix, body) =
            tag.unbindAll(this, toAvoid)
          val (others, realBody) =
            body.unbindAll(toAvoid ++ prefix.map(_._1), predicate)
          (prefix.map(p =>
            BinderSpec(tag, p._1, p._2: _*)) ++ others, realBody)
        case _ =>
          (Nil, this)
      }

    // cache shadowing-avoiding name for performance
    var shadowlessName: Option[String] = None

    // cache crossedNames for performance
    var crossedNames0: Option[Option[Set[String]]] = None
  }

  // literals
  case class LiteralGenus[T](man: Manifest[T]) extends Genus
  case class LiteralTag[T](man: Manifest[T]) extends LeafTag {
    final val genus = LiteralGenus(man)

    override def unparse(t: Tree) = t.as[T].toString
  }

  abstract class LeafFactory[T: Manifest](val tag: LeafTag) {
    require(tag.man == manifest[T])
    def genus: Genus = tag.genus
    def apply(x: T): ∙[T] = ∙(tag, x)
    def unapply(x: ∙[_]): Option[T] = x match {
      case y: ∙[_] if tag == y.tag => Some(y.as[T])
      case _ => None
    }
  }

  abstract class LiteralFactory[T: Manifest]
      extends LeafFactory[T](LiteralTag(manifest[T]))

  // string literals
  object § extends LiteralFactory[String]

  abstract class BinaryFactory(val tag: Tag) {
    def apply(x: Tree, y: Tree) = ⊹(tag, x, y)
    def unapply(t: ⊹): Option[(Tree, Tree)] = t match {
      case ⊹(tag, children @ _*) if tag == this.tag =>
        if (children.length == 2)
          Some((children(0), children(1)))
        else
          sys error s"""extractor contract violation, expect twins, has
            |$children""".stripMargin
      case _ => None
    }
  }
}
