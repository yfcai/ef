trait ExpressionGrammar extends Operators {
  def leftParens : Set[String] = "( { [ λ Λ ∀ ∃".words
  def rightParens: Set[String] = ") } ] . ,".words

  def forbidden: Set[String] = leftParens ++ rightParens

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

    override
    def getLeafTokens(items: Seq[Tree]): List[Token] =
      items.map(_.as[Token])(collection.breakOut)

    def unparseLeaf(leaf: ∙[_]): String =
      leaf.as[List[_]] mkString " "

    override def tryNext = Seq.empty[Seq[Operator]]
  }

  // for Λs
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

    // duplicate to create a token for each nonexisting nonterminal:
    // one variable is transformed into 2 to stand for
    // 1. the quantification
    // 2. the bound variable
    override
    def consTokens(tok: Token, toks: Seq[List[Token]]): List[Token] =
      toks match { case Seq(params, body) =>
        params.foldRight(body) {
          case (x, xs) => x :: x :: xs
        }
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

  // for λs
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
}

trait Syntax extends ExpressionGrammar {
  case object Type extends TopLevelGenus { def ops = typeOps }
  object æ extends AtomicFactory(FreeTypeVar)
  object ₌ extends BinaryFactory(TypeApplication)
  object → extends BinaryFactory(FunctionArrow)
  object ∀ extends QuantificationFactory(Universal)
  object ∃ extends QuantificationFactory(Existential)

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

  case object Universal extends Quantification {
    def symbol = Seq("∀", """\all""")
  }

  case object Existential extends Quantification {
    def symbol = Seq("∃", """\ex""")
  }

  case object Ascription extends BinaryOperator {
    def opGenus = BinaryOpGenus(Term, Type, Term)
    def lhs: Seq[Operator] = downFrom(Ascription, termOps)
    def rhs: Seq[Operator] = typeOps

    val fixity = Infixl(":")
  }

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

    val leftParen  = "{"
    val separator  = ","
    val rightParen = "}"

    val fixity = SetLike(leftParen, separator, rightParen)

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

  trait Quantification extends BinderOperator {
    def symbol: Any

    val fixity = Prefixr(symbol, dot)

    def genus = Type
    override
    def extraSubgenera = Seq(Annotation)
    def tryNext = Seq(Seq(Annotated), typeOps)
    def freeName = FreeTypeVar
    def prison = TypeVar

    override
    def cons(children: Seq[Tree]): Tree = children match {
      case Seq(Annotated(α, note), body) =>
        this.bind(α, note, body)
    }

    val collapsed = Collapsed(this)

    override def unparse(t: Tree): String = t match {
      case ⊹(tag, _, Annotation.none(), _) if tag == this =>
        collapsed.unparse(t)
      case _ if t.tag == this =>
        val (æ(α), Seq(note, body)) = unbind(t).get
        s"$getSymbol$α${note.unparse}$dot ${body.unparse}"
      case _ =>
        super.unparse(t)
    }

    def dot = "."

    def getSymbol: String = symbol match {
      case s: String => s
      case y: Seq[_] => y.head.toString
    }
  }

  case class Collapsed(binder: Quantification)
      extends Operator with CollapsedQuantification {
    val fixity = Prefixr(binder.symbol, binder.dot)
  }

  trait CollapsedQuantification extends Operator {
    def binder: Quantification
    def fixity: Fixity

    def tryNext = Seq(Seq(AtomList), typeOps)

    def genus = binder.genus
    override def subgenera: Option[Seq[Genus]] = Some(Seq(AtomList, genus))

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
      val i = bindings.indexWhere(_.annotation != Annotation.none())
      val j = if (i < 0) bindings.length else i
      val (collapsibles, uncollapsibles) = bindings.splitAt(j)
      bind(collapsibles.map(_.x), body.boundBy(uncollapsibles))
    }

    def expand(t: Tree): Tree = t match {
      case ⊹(tag, params @ ∙(AtomList, _), body) if tag == this =>
        params.as[Seq[String]].foldRight(body) {
          case (x, body) =>
            binder.bind(x, Annotation.none(), body)
        }
      case otherwise =>
        otherwise
    }

    // duplicate to create a token for each nonexisting nonterminal:
    // one variable is transformed into 5 to stand for
    // 1. the quantification
    // 2. the bound variable
    // 3. the nonexistent annotation (costs 3)
    override
    def consTokens(tok: Token, toks: Seq[List[Token]]): List[Token] =
      toks match { case Seq(params, body) =>
        params.foldRight(body) {
          case (x, xs) => x :: x :: x :: x :: x :: xs
        }
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

  abstract class QuantificationFactory(binder: Quantification) {
    def apply (α: String, note: Tree, body: Tree): Tree =
      binder.bind(α, note, body)

    def unapply(t: Tree): Option[(String, Tree, Tree)] =
      binder.unbind(t).map {
        case (α, Seq(note, body)) => (α.get, note, body)
      }
  }

  // an encoding of Option
  case object Nope extends LeafTag with Genus {
    def apply(): Tree = ∙[Unit](Nope, ())

    def unapply(t: Tree): Boolean = t.tag == this

    def man = manifest[Unit]
    def genus = this
  }

  case object Yeah extends Tag with Genus {
    def apply(t: Tree*): Tree = ⊹(this, t: _*)

    def unapplySeq(t: Tree): Option[Seq[Tree]] = t match {
      case ⊹(Yeah, subtree @ _*) => Some(subtree)
      case _ => None
    }

    def genus = this
  }

  case object Annotation extends Genus with Tag {
    def apply(parent: Option[String], debts: Option[Seq[Tree]]): Tree =
      ⊹(this, fromOption(parent.map(æ.apply)), fromOptions(debts))

    def unapply(t: Tree): Option[(Option[String], Option[Seq[Tree]])] =
      t match {
        case ⊹(Annotation, parent, debts) =>
          Some((toOption(parent).map(FreeTypeVar.get), toOptions(debts)))
        case _ =>
          None
      }

    // interconversion betwen options & trees
    // don't know how to reduce code duplication...
    def fromOption(opt: Option[Tree]): Tree = opt match {
      case None => Nope()
      case Some(t) => Yeah(t)
    }
    def fromOptions(opt: Option[Seq[Tree]]): Tree = opt match {
      case None => Nope()
      case Some(trees) => Yeah(trees: _*)
    }
    def toOption(t: Tree): Option[Tree] = t match {
      case Nope() => None
      case Yeah(t) => Some(t)
    }
    def toOptions(t: Tree): Option[Seq[Tree]] = t match {
      case Nope() => None
      case Yeah(trees @ _*) => Some(trees)
    }

    def genus = this

    override
    def unparse(t: Tree): String = t match {
      case Annotation(None, None) =>
        ""
      case Annotation(Some(parent), None) =>
        s" = $parent"
      case Annotation(None, Some(seq)) =>
        s" = ${TypeList.unparse(seq)}"
      case Annotation(Some(parent), Some(seq)) =>
        s" = $parent ${TypeList.unparse(seq)}"
    }

    object none {
      def apply(): Tree = _none
      def unapply(t: Tree): Boolean = t match {
        case Annotation(None, None) => true
        case _ => false
      }
      val _none = Annotation(None, None)
    }
  }

  case object Annotated extends Genus with Operator {
    def genus = this

    def apply(α: String, note: Tree): Tree = ⊹(this, §(α), note)

    def unapply(t: Tree): Option[(String, Tree)] = t match {
      case ⊹(Annotated, §(α), note) => Some((α, note))
      case _ => None
    }

    // parsing
    val fixity: Fixity = {
      val α = LoneToken.forbid(forbidden)
      val * = TypeList.fixity.composite
      α orElse
      α.andThenAfter("=", α orElse * orElse (α andThen1 *))
    }

    def tryNext: Seq[Seq[Operator]] = Seq.empty
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
          Annotated(α, Annotation(None, None))
        case Seq(æ(α), æ(β)) =>
          Annotated(α, Annotation(Some(β), None))
        case Seq(æ(α), TypeList(debts)) =>
          Annotated(α, Annotation(None, Some(debts)))
        case Seq(æ(α), æ(β), TypeList(debts)) =>
          Annotated(α, Annotation(Some(β), Some(debts)))
      }

    // produce tokens to fit the eventual AST
    override
    def consTokens(tok: Token, toks: Seq[List[Token]]): List[Token] =
      toks match {
        // ∙(LiteralTag(java.lang.String), α)
        // Annotation
        //   ∙(Nope, ())
        //   ∙(Nope, ())
        case Seq(List(α)) => α :: α :: α :: α :: Nil

        // ∙(LiteralTag(java.lang.String), α)
        // Annotation
        //   ∙(Nope, ())
        //   Yeah
        //
        // --OR--
        //
        // ∙(LiteralTag(java.lang.String), α)
        // Annotation
        //   Yeah
        //     TypeVar, bound of β
        //   ∙(Nope, ())
        case Seq(List(α), List(β)) =>
          if (β.body == TypeList.leftParen)
            α :: β :: β :: β :: Nil
          else
            α :: β :: β :: β :: β :: Nil

        // ∙(LiteralTag(java.lang.String), α)
        // Annotation
        //   ∙(Nope, ())
        //   Yeah
        //     TypeVar, bound of γ
        //     TypeVar, bound of δ
        case Seq(List(α), debts @ lp :: _) =>
          α :: lp :: lp :: debts

        // ∙(LiteralTag(java.lang.String), α)
        // Annotation
        //   Yeah
        //     TypeVar, bound of β
        //   Yeah
        //     TypeVar, bound of γ
        //     TypeVar, bound of δ
        case Seq(List(α), List(β), debts) =>
          α :: β :: β :: β :: debts
      }
  }

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
}
