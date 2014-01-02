/*
trait Types extends Trees {
  case object Type extends Genus
  // æ
}

trait Terms extends Types {
  // terms, no boilerplate
  case object Term extends Genus
  // try make them operators
  /*
  case object FreeVar extends FreeName(Term)
  case object Var extends DeBruijn(Term)
  case object Abs extends Binder(Var, Term, Term)
  case object App extends Tag(Term, Term, Term)

  // extrapolate BinderFactory after more examples
  object λ {
    def apply(x: String)(body: Tree): Tree =
      ⊹(Abs, §(x), body.imprison(Var, x, 0))
  }
  object χ extends LeafFactory[String](FreeVar)
   */
}*/

trait ExpressionGrammar extends Operators {
  // keywords (always a token by itself):
  val keywords = "( ) [ ] { } ∀ ∃ Λ λ .".words

  // things that can't be a name:
  val forbidden = "( ) .".words

  implicit class SplitStringIntoWords(s: String) {
    def words: Set[String] = Set(s split " ": _*)
  }

  trait TopLevelGenus extends Genus with Operator {
    def ops: Seq[Operator]

    def genus = this
    def fixity = CompositeItem
    override def parse(items: Seq[Tree]): Option[Tree] =
      ops findFirst (_ parse items)
    override def tryNext = Seq.empty[Seq[Operator]]
    override def cons(children: Seq[Tree]) =
      sys error s"cons of top-level genus $this"
  }

  trait Atomic extends LeafOperator with FreeName {
    def genus: Genus

    val fixity = LoneToken(forbidden)

    def cons(children: Seq[Tree]): Tree = children match {
      case Seq(∙(TokenAST, token: Token)) =>
        ∙(this, token.body)
      case _ =>
        sys error s"constructing atomic $this from $children"
    }

    def unparseLeaf(leaf: ∙[_]): String = leaf.as[String]
  }

  abstract class AtomicFactory(tag: Atomic) extends LeafFactory[String](tag)

  trait Parenthetic extends Operator {
    def genus: TopLevelGenus

    val fixity = LoneTree
    override def parse(items: Seq[Tree]): Option[Tree] = items match {
      case Seq(⊹(ProtoAST, children @ _*)) =>
        genus parse children
      case _ =>
        None
    }

    override def tryNext = Seq.empty[Seq[Operator]]
    override def cons(children: Seq[Tree]) =
      sys error s"cons of parenthetic $this"
  }

  case class BinaryOpGenus(lhs: Genus, rhs: Genus, result: Genus)

  // self-referential discipline
  // 1. superclass may define val
  // 2. subclass must provide def in general
  // 3. subclass may provide val if field isn't used to initialize
  //    superclass
  trait BinaryOperator extends Operator {
    def opGenus: BinaryOpGenus
    def fixity: Fixity
    def lhs: Seq[Operator]
    def rhs: Seq[Operator]

    val genus = opGenus.result
    override val subgenera = Some(Seq(opGenus.lhs, opGenus.rhs))
    lazy val tryNext = Seq(lhs, rhs)
    def cons(t: Seq[Tree]): Tree = t match {
      case Seq(lhs, rhs) => ⊹(this, lhs, rhs)
    }
  }

  trait Juxtapositional extends BinaryOperator {
    def elementGenus: Genus
    def lhs: Seq[Operator]
    def rhs: Seq[Operator]

    def opGenus = BinaryOpGenus(
      elementGenus, elementGenus, elementGenus)
    def fixity = Juxtaposition
  }

  trait Invocative extends BinaryOperator {
    def opGenus: BinaryOpGenus
    def ops: (String, String)
    def lhs: Seq[Operator]
    def rhs: Seq[Operator]

    val fixity = Postfix(ops._1, ops._2)
  }

  case object AtomList extends Genus with LeafOperator {
    def fixity = CompositeItem
    def genus = this
    def man = manifest[Seq[String]]

    override def precondition(items: Seq[Tree]): Boolean = {
      if (items.isEmpty)
        return false
      val areTokens = items foreach {
        case x @ ∙(TokenAST, _) if ! forbidden.contains(x.as[String]) =>
          ()
        case _ =>
          return false
      }
      true
    }

    def cons(children: Seq[Tree]): Tree =
      ∙(this, children.map(_.as[Token].body): Seq[String])

    def unparseLeaf(leaf: ∙[_]): String =
      leaf.as[List[_]] mkString " "

    override def tryNext = Seq.empty[Seq[Operator]]
  }

  // should be part of name binding language, shouldn't it?
  trait CollapsedBinder extends Operator {
    def binder: Binder
    def freeName: FreeName

    override def subgenera: Option[Seq[Genus]] =
      Some(Seq(AtomList, binder.genus))

    if (! binder.extraSubgenera.isEmpty)
      sys error s"can't collapse binders with extra annotations: $this"
    if (binder.prison.genus != freeName.genus)
      sys error s"can't collapse binder $binder incongruent with $freeName"

    override def parse(items: Seq[Tree]): Option[Tree] =
      super.parse(items).map(expand)

    override def unparse(t: Tree): String =
      super.unparse(collapse(t))

    def collapse(t: Tree): Tree = unbind(t).fold(t) {
      case (name, body) =>
        val collapsedBody = collapse(body)
        unbinds(collapsedBody).fold(binds(Seq(name), collapsedBody)) {
          case (names, body) => binds(name +: names, body)
        }
    }

    def expand(t: Tree): Tree = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        params.as[Seq[String]].foldRight(body) {
          case (x, body) => bind(x, body)
        }
      case otherwise =>
        otherwise
    }

    def bind(x: String, body: Tree): Tree =
      binder.bind(x, body)

    def binds(xs: Seq[String], body: Tree): Tree =
      ⊹(this, ∙(AtomList, xs), body)

    def unbind(t: Tree): Option[(String, Tree)] =
      binder.unbind(t) map { case (x, body, Seq()) => (x, body) }

    def unbinds(t: Tree): Option[(Seq[String], Tree)] = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        Some((params.as[Seq[String]], body))
      case _ =>
        None
    }
  }

  abstract class CollapsedBinderFactory(tag: CollapsedBinder) {
    def apply(x: String, body: Tree): Tree =
      tag.bind(x, body)

    def apply(xs: String*)(body: => Tree): Tree =
      tag.expand(tag.binds(xs, body))

    def unapply(t: ⊹): Option[(String, Tree)] = tag unbind t
  }
}

trait Syntax extends ExpressionGrammar {
  case object Type extends TopLevelGenus { def ops = typeOps }
  object æ extends AtomicFactory(FreeTypeVar)
  object ₌ extends BinaryFactory(TypeApplication)
  object → extends BinaryFactory(FunctionArrow)
  object ∀ extends CollapsedBinderFactory(CollapsedUniversals)
  object ∃ extends CollapsedBinderFactory(CollapsedExistentials)
  // write factories for bounded universals/existentials only if needed

  case object Term extends TopLevelGenus { def ops = termOps }
  object χ extends AtomicFactory(FreeVar)
  object ₋ extends BinaryFactory(Application)
  object □ extends BinaryFactory(Instantiation)
  object Å extends BinaryFactory(Ascription)

  case object FreeTypeVar extends Atomic   { def genus = Type }
  case object FreeVar     extends Atomic   { def genus = Term }
  case object TypeVar     extends DeBruijn { def genus = Type }
  case object Var         extends DeBruijn { def genus = Term }

  case object ParenthesizedType extends Parenthetic { def genus = Type }
  case object ParenthesizedTerm extends Parenthetic { def genus = Term }

  case object TypeApplication extends Juxtapositional {
    def elementGenus = Type
    def lhs = downFrom(TypeApplication, typeOps)
    def rhs = downFrom(ParenthesizedType, typeOps)
  }

  case object Application extends Juxtapositional {
    def elementGenus = Term
    def lhs = downFrom(Instantiation, termOps)
    def rhs = downFrom(ParenthesizedTerm, termOps)
  }

  case object Instantiation extends Invocative {
    def opGenus = BinaryOpGenus(Term, Type, Term)
    def ops = ("[", "]")
    def lhs = downFrom(Instantiation, termOps)
    def rhs = typeOps
  }

  case object FunctionArrow extends BinaryOperator {
    def opGenus = BinaryOpGenus(Type, Type, Type)
    def lhs: Seq[Operator] = downBelow(FunctionArrow, typeOps)
    def rhs: Seq[Operator] = typeOps

    val fixity = Infixr(Seq("→", "->"))
  }

  case object Ascription extends BinaryOperator {
    def opGenus = BinaryOpGenus(Term, Type, Term)
    def lhs: Seq[Operator] = downFrom(Ascription, termOps)
    def rhs: Seq[Operator] = typeOps

    val fixity = Infixl(":")
  }

  case object UniversalQuantification
      extends Binder with DelegateOperator {
    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
    def delegate = CollapsedUniversals
  }

  case object ExistentialQuantification
      extends Binder with DelegateOperator {
    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
    def delegate = CollapsedExistentials
  }

  val universalSymbol   = Seq("∀", """\all""")
  val existentialSymbol = Seq("∃", """\ex""")

  case object CollapsedUniversals
      extends CollapsedBinder with BinaryOperator {
    val fixity = Prefix(universalSymbol, ".")
    def opGenus = BinaryOpGenus(AtomList, Type, Type)
    def lhs = Seq(AtomList)
    def rhs = typeOps
    def binder = UniversalQuantification
    def freeName = FreeTypeVar
  }

  case object CollapsedExistentials
      extends CollapsedBinder with BinaryOperator {
    val fixity = Prefix(existentialSymbol, ".")
    def opGenus = BinaryOpGenus(AtomList, Type, Type)
    def lhs = Seq(AtomList)
    def rhs = typeOps
    def binder = ExistentialQuantification
    def freeName = FreeTypeVar
  }

  case object BoundedUniversal extends BoundedQuantification
  { def symbol = universalSymbol }

  case object BoundedExistential extends BoundedQuantification
  { def symbol = existentialSymbol }
/*
  case object TypeAbstraction extends Operator(
    Prefix("Λ", "."),
    Seq(Seq(TypeParameterList), termOps)
  )

  case object TermAbstraction extends Operator(
    Prefix("λ", ":", "."),
    Seq(Seq(Atomic), typeOps, termOps)
  )

  case object LetBinding extends Operator(
    Prefix("let", "=", "in"),
    Seq(Seq(Atomic), termOps, termOps)
  )
*/

  // common ground between λs and bounded quantifications
  trait AnnotatedBinderOp extends BinderOperator {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String]
    def endSymbol: Seq[String] = Seq(".")

    // fail fast
    override def precondition(items: Seq[Tree]): Boolean = {
      val x = items.take(3)
      x.length == 3 &&
        fixity.hasBody(x.head, symbol) &&
        fixity.hasBody(x.last, annotationSymbol)
    }

    val fixity = Prefix(symbol, annotationSymbol, endSymbol)
    lazy val tryNext = Seq(Seq(FreeTypeVar), typeOps, typeOps)

  }

  // common ground between bounded universals and existentials
  trait BoundedQuantification extends AnnotatedBinderOp {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String] = Seq("⊒")

    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
    override def extraSubgenera = Seq(Type)
  }

  val typeOps: List[Operator] =
    List(
      BoundedUniversal,
      BoundedExistential,
      UniversalQuantification,
      ExistentialQuantification,
      FunctionArrow,
      TypeApplication,
      ParenthesizedType,
      FreeTypeVar)

  val termOps: List[Operator] =
    List(
      Ascription,
      Instantiation,
      Application,
      ParenthesizedTerm,
      FreeVar)

  def downFrom(x: Operator, ops: List[Operator]): List[Operator] =
    ops match {
      case y :: tail if x == y => ops
      case _ :: tail => downFrom(x, tail)
      case Nil => sys error s"$x not found in $ops"
    }

  def downBelow(x: Operator, ops: List[Operator]): List[Operator] =
    downFrom(x, ops) match {
      case Nil | _ :: Nil => sys error s"nothing below $x in $ops"
      case x :: tail => tail
    }
}
