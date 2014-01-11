trait ExpressionGrammar extends Operators {
  def leftParens : Set[String] = "( { [ λ Λ ∀ ∃".words
  def rightParens: Set[String] = ") } ] . ,".words

  def forbidden: Set[String] = keywords

  implicit class SplitStringIntoWords(s: String) {
    def words: Set[String] = Set(s split " ": _*)
  }

  trait TopLevelGenus extends Genus with Operator {
    def ops: Seq[Operator]

    def apply(s: String): Tree = this.parse(s).get

    def genus = this
    def fixity = CompositeItem
    override def parse(items: Seq[Tree]) = ops findFirst (_ parse items)
    override def tryNext = Seq.empty[Seq[Operator]]
    override def cons(children: Seq[Tree]) =
      sys error s"cons of top-level genus $this"
  }

  trait Atomic extends LeafOperator with FreeName {
    def genus: Genus
    val fixity = LoneToken.forbid(forbidden)

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
    override def parse(items: Seq[Tree]) = items match {
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
    override def subgenera: Option[Seq[Genus]] =
      Some(Seq(opGenus.lhs, opGenus.rhs))
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

    val fixity = Postfixl(ops._1, ops._2)
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
  // @param genus has to be class parameter because "val genus"
  // is taken in trait BinaryOperator and it doesn't make sense
  // to declare something like "genus0".
  abstract class CollapsedBinder(_genus: TopLevelGenus)
      extends BinaryOperator {
    def binder: Binder

    def opGenus = BinaryOpGenus(AtomList, _genus, _genus)
    def lhs = Seq(AtomList)
    def rhs = _genus.ops // can override if want some other precedence
    def freeName: FreeName = binder.freeName

    if (binder.genus != _genus)
      sys error s"$this can't collapse binder $binder to ${_genus}"
    if (! binder.extraSubgenera.isEmpty)
      sys error s"can't collapse binders with extra annotations: $this"

    override def parse(items: Seq[Tree]) =
      super.parse(items).map { case (t, toks) => (expand(t), toks) }

    override def unparse(t: Tree): String =
      super.unparse(collapse(t))

    def collapse(t: Tree): Tree = binder.unbind(t).fold(t) {
      case (name, Seq(body)) =>
        val collapsedBody = collapse(body)
        unbind(collapsedBody).fold(bind(Seq(name.get), collapsedBody)) {
          case (names, body) => bind(name.get +: names, body)
        }
    }

    def expand(t: Tree): Tree = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        params.as[Seq[String]].foldRight(body) {
          case (x, body) => binder.bind(x, body)
        }
      case otherwise =>
        otherwise
    }

    def bind(xs: Seq[String], body: Tree): Tree =
      ⊹(this, ∙(AtomList, xs), body)

    def unbind(t: Tree): Option[(Seq[String], Tree)] = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        Some((params.as[Seq[String]], body))
      case _ =>
        None
    }
  }

  abstract class CollapsedBinderFactory(tag: CollapsedBinder) {
    def apply(x: String, body: Tree): Tree =
      tag.binder.bind(x, body)

    def apply(xs: String*)(body: => Tree): Tree =
      tag.expand(tag.bind(xs, body))

    def unapplySeq(t: ⊹): Option[(∙[String], Seq[Tree])] =
      tag.binder.unbind(t)
  }


  // common ground between λs and bounded quantifications
  trait AnnotatedBinderOp extends BinderOperator with Symbolic {
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

    val fixity = Prefixr(symbol, annotationSymbol, endSymbol)
  }

  abstract class AnnotatedBinderFactory(tag: AnnotatedBinderOp) {
    def apply(x: String, annotation: Tree, body: Tree): Tree =
      tag.bind(x, annotation, body)

    def unapply(t: Tree): Option[(String, Tree, Tree)] =
      tag.unbind(t).map {
        case (∙(_, x), Seq(annotation, body)) => (x, annotation, body)
      }
  }

  trait Symbolic {
    def symbol: Seq[String]
  }
}

trait Syntax extends ExpressionGrammar {
  case object Type extends TopLevelGenus { def ops = typeOps }
  object æ extends AtomicFactory(FreeTypeVar)
  object ₌ extends BinaryFactory(TypeApplication)
  object → extends BinaryFactory(FunctionArrow)

  object ∀ extends CollapsedBinderFactory(CollapsedUniversals)
  object ∃ extends CollapsedBinderFactory(CollapsedExistentials)

  object ∀? extends AnnotatedBinderFactory(UniversalUncertainty)
  object ∃? extends AnnotatedBinderFactory(ExistentialUncertainty)
  object ∀= extends AnnotatedBinderFactory(UniversalBound)
  object ∃= extends AnnotatedBinderFactory(ExistentialBound)

  case object Term extends TopLevelGenus { def ops = termOps }
  object χ extends AtomicFactory(FreeVar)
  object ₋ extends BinaryFactory(Application)
  object □ extends BinaryFactory(Instantiation)
  object Å extends BinaryFactory(Ascription)
  object λ extends AnnotatedBinderFactory(AnnotatedAbstraction)

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

  case object UniversalQuantification extends DelegateTypeBinder
  { def delegate = CollapsedUniversals }

  case object ExistentialQuantification extends DelegateTypeBinder
  { def delegate = CollapsedExistentials }

  case object CollapsedUniversals
      extends CollapsedBinder(Type) with Universals {
    val fixity = Prefixr(symbol, ".")
    def binder = UniversalQuantification
  }

  case object CollapsedExistentials
      extends CollapsedBinder(Type) with Existentials {
    val fixity = Prefixr(symbol, ".")
    def binder = ExistentialQuantification
  }

  case object UniversalBound
      extends BoundedQuantification
         with Universals

  case object ExistentialBound
      extends BoundedQuantification
         with Existentials

  case object UniversalUncertainty
      extends UncertainQuantification
         with Universals

  case object ExistentialUncertainty
      extends UncertainQuantification
         with Existentials

  case object TypeAbstraction extends Binder with DelegateOperator {
    def genus = Term
    def prison = TypeVar
    def freeName = FreeTypeVar
    def delegate = CollapsedTypeAbstractions
  }

  case object CollapsedTypeAbstractions extends CollapsedBinder(Term) {
    val fixity = Prefixr(Seq("Λ", """\Tabs"""), ".")
    def binder = TypeAbstraction
  }

  case object AnnotatedAbstraction extends AnnotatedBinderOp {
    def symbol = Seq("λ", """\abs""")
    def annotationSymbol = Seq(":")

    def genus = Term
    def prison = Var
    def freeName = FreeVar
    override def extraSubgenera = Seq(Type)
    lazy val tryNext = Seq(Seq(FreeVar), typeOps, termOps)
  }

  case object CStyleConditional extends Operator {
    final val fixity = Infixr("?", ":")
    lazy val tryNext =
      Seq(downBelow(this, termOps),
          downBelow(this, termOps),
          downFrom (this, termOps))

    def genus = Term
    override def subgenera = Some(Seq(Term, Term, Term))
    def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)
  }

  case object TypeList
      extends Genus
         with LeafOperator
         with KnownLeafTag[Seq[Tree]] {
    def apply(seq: Tree*): Tree = cons(seq)
    def unapply(t: Tree): Option[Seq[Tree]] = t match {
      case t @ ∙(TypeList, _) => Some(t.as[Seq[Tree]])
      case _ => None
    }

    def man = manifest[Seq[Tree]]
    def genus = this

    val fixity = SetLike("{", ",", "}")

    override def tryNextOverride: Seq[Seq[Tree]] => Seq[Seq[Operator]] =
      _.map(_ => typeOps)

    def cons(children: Seq[Tree]): Tree = ∙(TypeList, children)

    def unparseLeaf(leaf: ∙[_]): String = leaf match {
      case types @ ∙(TypeList, _) =>
        unparse(types.as[Seq[Tree]])
    }

    def unparse(seq: Seq[Tree]): String =
      s"{${seq.map(_.unparse).mkString(", ")}}"
  }

  // subsets of language constructs

  trait DelegateTypeBinder extends Binder with DelegateOperator {
    def delegate: Operator

    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
  }

  trait UncertainQuantification extends MultiplyAnnotatedQuantification {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String] = Seq("=")
  }

  trait BoundedQuantification extends AnnotatedQuantification {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String] = Seq("=")
  }

  trait MultiplyAnnotatedQuantification extends AnnotatedBinderOp {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String]

    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
    override def extraSubgenera = Seq(TypeList)
    lazy val tryNext = Seq(Seq(FreeTypeVar), Seq(TypeList), typeOps)
  }

  trait AnnotatedQuantification extends AnnotatedBinderOp {
    def symbol: Seq[String]
    def annotationSymbol: Seq[String]

    def genus = Type
    def prison = TypeVar
    def freeName = FreeTypeVar
    override def extraSubgenera = Seq(Type)
    lazy val tryNext = Seq(Seq(FreeTypeVar), Seq(Type), typeOps)
  }

  trait Universals extends Symbolic {
    def symbol = Seq("∀", """\all""")
  }

  trait Existentials extends Symbolic {
    def symbol = Seq("∃", """\ex""")
  }


  case object Universal extends Quantification {
    def symbol = Seq("∀", """\all""")
  }

  case object Existential extends Quantification {
    def symbol = Seq("∃", """\ex""")
  }

  trait Quantification extends BinderOperator {
    def symbol: Any

    val fixity = Prefixr(symbol, dot)

    def genus = Type
    override
    def extraSubgenera = Seq(Annotation)
    def tryNext = Seq(Seq(Annotation), typeOps)
    def freeName = FreeTypeVar
    def prison = TypeVar

    override def cons(children: Seq[Tree]): Tree = children match {
      case Seq(note @ ♬(α, _, _), body) =>
        this.bind(α, note, body)
    }

    val collapsed = Collapsed(this)

    override def unparse(t: Tree): String = t match {
      case ⊹(tag, _, ♬(_, None, None), _) if tag == this =>
        collapsed.unparse(t)
      case _ if t.tag == this =>
        val (æ(α), Seq(note, body)) = unbind(t).get
        val newNote = note.as[Annotation].updated(α)
        s"$getSymbol${newNote.unparse}$dot ${body.unparse}"
      case _ =>
        super.unparse(t)
    }

    def dot = "."

    def getSymbol: String = symbol match {
      case s: String => s
      case y: Seq[_] => y.head.toString
    }
  }

  case class Collapsed(binder: Quantification) extends Operator {
    val fixity = Prefixr(binder.symbol, binder.dot)
    def tryNext = Seq(Seq(AtomList), typeOps)

    def genus = binder.genus
    override def subgenera = Some(Seq(AtomList, genus))

    def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)

    override def parse(items: Seq[Tree]) =
      super.parse(items).map { case (t, toks) => (expand(t), toks) }

    override def unparse(t: Tree): String = unbind(collapse(t)).get match {
      case (params, body) =>
        s"${binder.getSymbol}${params.mkString(" ")}"+
        s"${binder.dot} ${body.unparse}"
    }

    def collapse(t: Tree): Tree = {
      val (bindings, body) = t.unbindAll(binder)
      val i = bindings.indexWhere(spec => spec.annotation != ♬(spec.x))
      val j = if (i < 0) bindings.length else i
      val (collapsibles, uncollapsibles) = bindings.splitAt(j)
      bind(collapsibles.map(_.x), body.boundBy(uncollapsibles))
    }

    def expand(t: Tree): Tree = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        params.as[Seq[String]].foldRight(body) {
          case (x, body) => binder.bind(x, ♬(x), body)
        }
      case otherwise =>
        otherwise
    }

    def bind(xs: Seq[String], body: Tree): Tree =
      if (xs.isEmpty)
        body
      else
        ⊹(this, ∙(AtomList, xs), body)

    def unbind(t: Tree): Option[(Seq[String], Tree)] = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        Some((params.as[Seq[String]], body))
      case _ =>
        None
    }
  }

  case class Annotation(
    alpha : String,
    parent: Option[String],
    debts : Option[Seq[Tree]]) {

    def toTree: Tree = ∙(Annotation, this)

    def unparse: String = this match {
      case Annotation(α, None, None) =>
        α
      case Annotation(α, Some(parent), None) =>
        s"$α = $parent"
      case Annotation(α, None, Some(seq)) =>
        s"$α = ${TypeList.unparse(seq)}"
      case Annotation(α, Some(parent), Some(seq)) =>
        s"$α = $parent ${TypeList.unparse(seq)}"
    }

    def updated(α: String) = Annotation(α, parent, debts)
  }

  // annotation constructors & destructor
  object ♬ {
    def apply(α: String): Tree =
      Annotation(α, None, None).toTree
    def apply(α: String, β: String): Tree =
      Annotation(α, Some(β), None).toTree
    def apply(α: String, debts: Seq[Tree]): Tree =
      Annotation(α, None, Some(debts)).toTree
    def apply(α: String, β: String, debts: Seq[Tree]): Tree =
      Annotation(α, Some(β), Some(debts)).toTree

    def unapply(t: Tree):
        Option[(String, Option[String], Option[Seq[Tree]])] = t match {
      case ∙(Annotation, Annotation(α, parent, debts)) =>
        Some((α, parent, debts))
      case _ =>
        None
    }
  }

  case object Annotation
      extends Genus
         with LeafOperator
         with KnownLeafTag[Annotation] {
    def man = manifest[Annotation]
    def genus = this

    val fixity: Fixity = {
      val α = LoneToken.forbid(forbidden)
      val * = TypeList.fixity.composite
      α orElse
      α.andThenAfter("=", α orElse * orElse (α andThen1 *))
    }

    override def tryNextOverride: Seq[Seq[Tree]] => Seq[Seq[Operator]] =
      stuff => stuff.length match {
        case 1 => Seq(Seq(FreeTypeVar))
        case 2 => Seq(Seq(FreeTypeVar), Seq(FreeTypeVar, TypeList))
        case 3 => Seq(Seq(FreeTypeVar), Seq(FreeTypeVar), Seq(TypeList))
        case _ => sys error s"\n\n$stuff\n\n"
      }

    def cons(children: Seq[Tree]): Tree =
      children match {
        case Seq(æ(α)) =>
          ♬(α)
        case Seq(æ(α), æ(β)) =>
          ♬(α, β)
        case Seq(æ(α), TypeList(debts)) =>
          ♬(α, debts)
        case Seq(æ(α), æ(β), TypeList(debts)) =>
          ♬(α, β, debts)
      }

    def unparseLeaf(leaf: ∙[_]): String = leaf.as[Annotation].unparse
  }


  val typeOps: List[Operator] =
    List(
      Universal,
      Universal.collapsed,
      Existential,
      Existential.collapsed,
      FunctionArrow,
      TypeApplication,
      ParenthesizedType,
      FreeTypeVar)

  val termOps: List[Operator] =
    List(
      TypeAbstraction,
      AnnotatedAbstraction,
      CStyleConditional,
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

  // BINDERPREFIX

  type BinderPrefix = Map[String, BinderSpec]

  def pretty(spec: BinderSpec): String = {
    val (α, notes) = (spec.x, spec.annotations)
    spec.tag match {
      case UniversalBound            => s"∀$α = ${notes.head.unparse}"
      case ExistentialBound          => s"∃$α = ${notes.head.unparse}"
      case UniversalQuantification   => s"∀$α"
      case ExistentialQuantification => s"∃$α"
    }
  }

  def pretty(Q: BinderPrefix): String =
    pretty(linearizePrefix(Q))

  def pretty(Q: Seq[BinderSpec]): String =
    Q.map(pretty).mkString("\n")

  def topologicalOrder(Q: BinderPrefix): Map[String, Int] = {
    val graph = Q map { case (α, spec) => (α, spec.annotation.freeNames) }
    var distance = -1
    var toVisit  = graph.keySet
    var result   = Map.empty[String, Int]
    while (! toVisit.isEmpty) {
      val frontier = toVisit.filter {
        α => graph(α).find(toVisit contains _) == None
      }
      if (frontier.isEmpty)
        sys error s"cycle detected in prefix\n${pretty(Q)}"
      distance = distance +  1
      toVisit  = toVisit  -- frontier
      result   = result   ++ frontier.map(α => (α, distance))
    }
    result
  }

  // sort by topological order first and then by lexicographical order
  def linearizePrefix(Q: BinderPrefix): Seq[BinderSpec] = {
    val topo = topologicalOrder(Q)
    Q.map({ case (α, τ) => (τ, (topo(α), α)) }).toList.
      sortBy(_._2).map(_._1)
  }

  trait Status[+T] {
    def toBoolean: Boolean
    def get: T
    def map[R](f: T => R): Status[R]
  }
  case class Success[+T](get: T) extends Status[T] {
    def toBoolean: Boolean = true
    def map[R](f: T => R): Status[R] = Success(f(get))
  }
  case class Failure[+T](message: String) extends Status[T] {
    def toBoolean: Boolean = false
    def map[R](f: T => R): Status[R] = Failure(message)

    def get: T = sys error s"get of $this"
  }
}
