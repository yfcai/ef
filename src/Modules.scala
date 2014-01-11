// parse file, produce AST
trait Modules extends Syntax {
  case object ParagraphExpr extends TopLevelGenus {
    val ops = List(TypeSynonym, Signature, Definition)
  }

  case object TypeSynonym
      extends CollapsedQuantification with Definitional {
    val fixity = Prefixr("type", "=")
    def binder = Universal

    def sanityCheck(t: Tree, tok: Token) =
      if (binder.count(t) != 0)
        throw Problem(tok, "recursive type synonym")

    override def subgenera = super[Definitional].subgenera

    override def unparse(t: Tree): String = t match {
      case ⊹(TypeSynonym, x, body) =>
        s"type ${x.unparse} = ${body.unparse}"
    }
  }

  case object Definition extends UnaryDefinitional {
    def defSymbol = "="
    def opGenus = BinaryOpGenus(Term, Term, Term)
    def lhs = Seq(FreeVar)
    def rhs = Term.ops
  }

  case object Signature extends UnaryDefinitional {
    def defSymbol = ":"
    def opGenus = BinaryOpGenus(Term, Type, Term)
    def lhs = Seq(FreeVar)
    def rhs = Type.ops
  }

  trait Definitional extends Operator {
    def sanityCheck(t: Tree, tok: Token): Unit

    override def subgenera: Option[Seq[Genus]] = None

    override def parse(items: Seq[Tree]): Option[(Tree, List[Token])] =
      super.parse(items).map({
        case result @ (t, toks) => sanityCheck(t, toks.head) ; result
      }).map {
        case (t @ ⊹(binder: Binder, _*), toks) =>
          val (x, Seq(_, body)) = binder.unbind(t).get
          (⊹(this, x, body), toks)
        case otherwise =>
          otherwise
      }

    // SUBCLASSES OF DEFINITIONAL HAS TO OVERRIDE UNPARSE

    def unparse(x: String, body: Tree): String =
      unparse(⊹(this, §(x), body))

    // can be used to deconstruct trees
    // inverse of post processing after "parse"
    def unapply(t: Tree): Option[(String, Tree)] = t match {
      case ⊹(tag, x, body) if tag == this =>
        Some((x.as[String], body))
      case _ => None
    }
  }

  trait UnaryDefinitional
      extends Definitional with BinaryOperator {
    def defSymbol: String
    def opGenus: BinaryOpGenus
    def lhs: Seq[Operator]
    def rhs: Seq[Operator]

    final val fixity: Fixity = Infixr(defSymbol)

    override def subgenera = super[Definitional].subgenera

    override def precondition(items: Seq[Tree]) =
      items.take(2).length == 2 && fixity.hasBody(items(1), defSymbol)

    def sanityCheck(t: Tree, tok: Token): Unit = t match {
      case ⊹(_, x, xdef) =>
        if (xdef.count(x) != 0)
          throw Problem(tok, "recursive definition")
    }
  }

  case class Module
  ( syn    : Map[String, Tree       ] ,
    syntoks: Map[String, List[Token]] ,
    sig    : Map[String, Tree       ] ,
    sigtoks: Map[String, List[Token]] ,
    dfn    : Map[String, Tree       ] ,
    dfntoks: Map[String, List[Token]] ) {

    def unparse: String = {
      type Domain = List[(Int, Definitional, String, Tree)]
      def acc(toks: Map[String, List[Token]], op: Definitional)
        (p: (String, Tree), accumulator: Domain) =
        (toks(p._1).head.line, op, p._1, p._2) :: accumulator
      spaceParagraphs(
        dfn.foldRight(
          sig.foldRight(
            syn.foldRight(
              Nil: Domain
            )(acc(syntoks, TypeSynonym))
          )(acc(sigtoks, Signature))
        )(acc(dfntoks, Definition)).sortBy(_._1))
    }

    def spaceParagraphs(list: List[(Int, Definitional, String, Tree)]):
        String = list match {
      case x :: rest =>
        val f: ((Int, Definitional, String, Tree)) => String = {
          case (_, op, x, xdef) => op.unparse(x, xdef)
        }
        (f(x) :: list.zip(rest).flatMap({
          case (prev @ (_, Signature , x, _),
                next @ (_, Definition, y, _)) if x == y =>
            List("\n", f(next))
          case (_, next) =>
            List("\n\n", f(next))
        })).mkString
      case Nil => ""
    }

    def ensureUnique(map: Map[String, _], s: String, tok: Token): Unit =
      if (map contains s)
        throw Problem(tok, "repeated top level name")

    // tentative type. write use case first.
    def add(t: Tree, toks: List[Token]): Module = t match {
      case TypeSynonym(α, τ) =>
        ensureUnique(syn, α, toks.head)
        Module(
          syn.updated(α, τ), syntoks.updated(α, toks),
          sig, sigtoks,
          dfn, dfntoks)
      case Signature(x, τ) =>
        ensureUnique(sig, x, toks.head)
        Module(
          syn, syntoks,
          sig.updated(x, τ), sigtoks.updated(x, toks),
          dfn, dfntoks)
      case Definition(x, t) =>
        ensureUnique(dfn, x, toks.head)
        Module(
          syn, syntoks,
          sig, sigtoks,
          dfn.updated(x, t), dfntoks.updated(x, toks))
      case _ =>
        sys error s"undetected parse error on:\n${t.unparse}"
    }
  }

  object Module {
    def empty: Module =
      Module(Map.empty, Map.empty, Map.empty,
             Map.empty, Map.empty, Map.empty)

    def fromFile(file: String): Module =
      Paragraphs.fromFile(file).foldLeft(empty) {
        case (module, paragraph) =>
          val tokens = tokenize(paragraph)
          ParagraphExpr.parse(ProtoAST(tokens)) match {
            case Some((tree, toks)) =>
              module.add(tree, toks)
            case None =>
              throw Problem(tokens.head,
                s"can't parse this paragraph:\n${paragraph.body}")
          }
      }
  }
}
