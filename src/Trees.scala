/** Conor McBride and James McKinna:
  * I am not a number---I am a free variable
  */

import scala.language.implicitConversions

trait Trees {
  trait Genus // type, terms, etc

  trait Tag {
    def genus: Genus

    // subgenera is optional. if tree is variadic, no subgenera
    // makes sense.
    def subgenera: Option[Seq[Genus]] = None

    // extension point: pretty printer
    def unparse(t: Tree): String = t.print
  }

  // tag for variadic untyped trees
  trait UnclassifiedTag extends Tag with Genus { def genus = this }

  trait TreeF[T] {
    def tag: Tag
    def children: Seq[T]

    def map[S](f: T => S): TreeF[S] = this match {
      case ∙:(tag, get) => ∙:(tag, get)
      case ⊹:(tag, children @ _*) => ⊹:(tag, children map f: _*)
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
    override final val subgenera = Some(Nil)
  }

  trait FreeName extends LeafTag { final val man = manifest[String] }
  trait DeBruijn extends LeafTag { final val man = manifest[Int   ] }

  /** subscript utilities */
  object Subscript {
    // Subscript.s
    val s = "₀₁₂₃₄₅₆₇₈₉"

    def is(c: Char): Boolean = s contains c

    def remove(subscribedName: String): String = {
      val j = subscribedName.lastIndexWhere(c => ! is(c))
      if (j >= 0)
        subscribedName.substring(0, j + 1)
      else
        subscribedName
    }

    def apply(i: Int): String = i.toString map (c => s(c - '0'))
  }

  trait Binder extends Tag
  {
    def prison        : DeBruijn
    def freeName      : FreeName
    def genus         : Genus
    def extraSubgenera: Seq[Genus] = Nil
    // in subclasses, extraSubgenera should always be a "def", not "val",
    // to avoid NullPointerException during initialization

    if (prison.genus != freeName.genus)
      sys error s"""|binder $this changes prisoners' identity from
        |${freeName.genus} to ${prison.genus}
        |""".stripMargin

    override final val subgenera =
      Some(§.genus +: (extraSubgenera :+ genus))

    def        bodyOf(t: Tree): Tree   = t.children.last
    def defaultNameOf(t: Tree): String = t.children.head.as[String]
    def annotationsOf(t: Tree): Seq[Tree] = t.children.tail.init

    def bindingGenus: Genus = prison.genus

    // bind a free name
    def bind(x: String, trees: Tree*): Tree = {
      val (annotations, b) = trees.splitAt(trees.length - 1)
      ⊹(this, §(x) +: (annotations :+ b.head.imprison(prison, x, 0)): _*)
    }

    // free a bound number
    def unbind(t: Tree): Option[(String, Seq[Tree])] = t match {
      case ⊹(tag, _*) if tag == this =>
        val name = nameOf(t)
        Some((name, annotationsOf(t) :+ t(∙(freeName, name))))
      case _ =>
        None
    }

    def imprison(x: String, body: Tree): Tree =
      body.imprison(prison, x, 0)

    // name discovery in a namespace
    def nameOf(t: Tree): String = nameOf(t, Set.empty)

    def nameOf(t: Tree, _toAvoid: Set[String]): String = {
      val toAvoid = _toAvoid ++ t.freeNames ++
        crossedNames(bodyOf(t), 0).fold(Set.empty[String])(identity)
      val startingID  = -1
      val defaultName = Subscript.remove(defaultNameOf(t))
      var i = startingID
      var x = defaultName
      while (toAvoid contains x) {
        i = i + 1
        if (i == startingID) sys error "ran outta names"
        x = defaultName + Subscript(i)
      }
      x
    }

    // names of binders crossing a back-reference path
    // with the same prison
    def crossedNames(t: Tree, i: Int): Option[Set[String]] = t match {
      case ⊹(tag: Binder, children @ _*) =>
        collectOptions(children.map(x => crossedNames(x, i + 1)))(_ ++ _).
          map { x =>
            if (tag.prison == this.prison) // name-spacing
              x + tag.nameOf(t)
            else
              x
          }
      case ⊹(tag, children @ _*) =>
        collectOptions(children map { x => crossedNames(x, i) })(_ ++ _)
      case ∙(tag: DeBruijn, j) if j == i =>
        Some(Set.empty[String])
      case _ =>
        None
    }

    def collectOptions[S](x: Seq[Option[S]])(op: (S, S) => S): Option[S] = {
      val existing = x withFilter (_ != None) map (_.get)
      if (existing.isEmpty)
        None
      else
        Some(existing.tail.fold(existing.head)(op))
    }
  }


  // branches and leafs, worthy of boilerplates
  class ∙[S: Manifest](tag: LeafTag, get: S)
      extends ∙:[Tree, S](tag, get) with Tree {
    if (tag.man != manifest[S])
      sys error s"""|incongruent manifests in leaves.
        |declared: ${tag.man}
        |actual  : ${manifest[S]}
        |""".stripMargin
    override def toString = s"∙($tag, $get)"
  }
  class ⊹(tag: Tag, children: Tree*)
      extends ⊹:[Tree](tag, children: _*) with Tree {
    override def toString =
      s"⊹($tag, ${children.map(_.toString).mkString(", ")})"
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
      case ∙:(tag, get) => ∙(tag, get)
      case ⊹:(tag, children @ _*) => ⊹(tag, children: _*)
    }
  }

  trait Tree extends TreeF[Tree] {
    // dynamic type safety, may disable for performance
    if (tag.subgenera != None &&
        children.map(_.tag.genus) != tag.subgenera.get)
      sys error s"""|subgenera mismatch
        |${tag.subgenera.get.toString}
        |${this.print}
        |""".stripMargin

    def fold[S](f: TreeF[S] => S): S = f(this map (_ fold f))

    // substitution of variable bound here
    // (only works on binders)
    def apply(xdef: Tree): Tree = tag match {
      case tag: Binder =>
        require(tag.bindingGenus == xdef.tag.genus)
        tag bodyOf this subst (0, xdef)
      case _ =>
        sys error s"expect binder, got: ${this.print}"
    }

    // substitution of bound variable
    def subst(i: Int, xdef: Tree): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag, children map (_.subst(i + 1, xdef)): _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag, children map (_.subst(i, xdef)): _*)
      case ∙(tag: DeBruijn, j: Int) if i == j =>
        require(xdef.tag.genus == tag.genus)
        xdef.shift(i, 0)
      case otherwise =>
        otherwise
    }

    // put a free variable in prison, give it numbers
    def imprison(prison: DeBruijn, x: String, i: Int): Tree =
      this match {
        case ⊹(tag: Binder, children @ _*) =>
          ⊹(tag, children map (_.imprison(prison, x, i + 1)): _*)
        case ⊹(tag, children @ _*) =>
          ⊹(tag, children map (_.imprison(prison, x, i)): _*)
        case ∙(tag: FreeName, get) if get == x =>
          require(tag.genus == prison.genus) // shan't bind typevar by λ
          ∙(prison, i)
        case otherwise =>
          otherwise
      }

    // d-place shift of this above cutoff c
    def shift(d: Int, c: Int): Tree = this match {
      case ⊹(tag: Binder, children @ _*) =>
        ⊹(tag, children map (_.shift(d, c + 1)): _*)
      case ⊹(tag, children @ _*) =>
        ⊹(tag, children map (_.shift( d, c)): _*)
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

    // collect free names with tag equal to mine
    def freeNames: Set[String] = fold[Set[String]] {
      case ∙:(tag: FreeName, get: String) if tag.genus == this.tag.genus =>
        Set(get)
      case ∙:(tag, get) =>
        Set.empty
      case otherwise =>
        allFreeNamesAlgebra(otherwise)
    }

    // collect all free names
    def allFreeNames: Set[String] = fold(allFreeNamesAlgebra)

    def allFreeNamesAlgebra: TreeF[Set[String]] => Set[String] = {
      case ⊹:(tag, children @ _*) =>
        children.fold(Set.empty[String])(_ ++ _)
      case ∙:(tag: FreeName, get: String) =>
        Set(get)
      case _ =>
        Set.empty
    }

    // traversals
    def preorder: Iterator[Tree] = this match {
      case ∙(_, _) => Iterator(this)
      case ⊹(_, children @ _*) => Iterator(this) ++
        children.flatMap(_.preorder) // ++ is call-by-name for iterators
    }
  }

  // literals
  case class LiteralGenus[T](man: Manifest[T]) extends Genus
  case class LiteralTag[T](man: Manifest[T]) extends LeafTag {
    final val genus = LiteralGenus(man)
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
