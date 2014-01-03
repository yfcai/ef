// parse file, produce AST
trait Modules extends Syntax {
  case object TypeSynonym
      extends CollapsedBinder(Type) with Definitional {
    val fixity = Prefix("type", "=")
    def binder = UniversalQuantification

    def sanityCheck(t: Tree, tok: Token) =
      if (binder.count(t) != 0)
        throw Problem(tok, "recursive type synonym")
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

  trait Definitional extends BinaryOperator {
    def sanityCheck(t: Tree, tok: Token): Unit

    override def subgenera: Option[Seq[Genus]] = None

    override def parse(items: Seq[Tree]): Option[(Tree, List[Token])] =
      super.parse(items).map({
        case result @ (t, toks) => sanityCheck(t, toks.head) ; result
      }).map {
        case (t @ ⊹(binder: Binder, _*), toks) =>
          val (x, Seq(body)) = binder.unbind(t).get
          (⊹(this, x, body), toks)
        case otherwise =>
          otherwise
      }

    // can be used to deconstruct trees
    // inverse of post processing after "parse"
    def unapply(t: Tree): Option[(∙[String], Tree)] = t match {
      case ⊹(tag, x, body) if tag == this =>
        Some((x.asInstanceOf[∙[String]], body))
      case _ => None
    }
  }

  abstract class UnaryDefinitional extends Definitional {
    def defSymbol: String
    def opGenus: BinaryOpGenus
    def lhs: Seq[Operator]
    def rhs: Seq[Operator]

    final val fixity: Fixity = Infixr(defSymbol)

    override def precondition(items: Seq[Tree]) =
      items.take(2).length == 2 && fixity.hasBody(items(1), defSymbol)

    def sanityCheck(t: Tree, tok: Token): Unit = t match {
      case ⊹(_, x, xdef) =>
        if (xdef.count(x) != 0)
          throw Problem(tok, "recursive definition")
    }
  }

/*
  case object ParagraphExpr extends DummyOperator(paragraphOps) {
    def fromFileWithLines(path: String): Iterator[(AST, Int)] =
      (Paragraphs fromFile path) map {
        p => (fromParagraph(path.split("/").last)(p), p.line)
      }

    def fromFile(path: String): Iterator[AST] =
      (Paragraphs fromFile path) map fromParagraph(path.split("/").last)

    def withLines(string: String): Iterator[(AST, Int)] =
      Paragraphs(string) map {
        p => (fromParagraph("#LINE")(p), p.line)
      }

    def apply(string: String): Iterator[AST] =
      Paragraphs(string) map fromParagraph("#LINE")

    def fromParagraph(path: String)(paragraph: Paragraph): AST =
      parse(paragraph.body) match {
        case None =>
          sys error s"\n$path:${paragraph.line}   PARSE ERROR\n"
        case Some(ast) =>
          ast
      }
  }

  val paragraphOps: List[Operator] =
    List(
      ParagraphComment,
      TypeSynonym,
      TypeSignature,
      TermDefinition,
      TypedFUnctionDefinition)
 */
}

/*
trait ASTConversions extends ExpressionGrammar with Terms {
  implicit class ConversionsFromTypeToOperator(τ: Type) {
    def toAST: AST = τ match {
      case α(binder) =>
        Leaf(Atomic, Seq(Seq(binder.name)))
      case δ(name) =>
        Leaf(Atomic, Seq(Seq(name)))
      case all: ∀ =>
        unnestBinders(all, UniversalQuantification)
      case ex: ∃ =>
        unnestBinders(ex , ExistentialQuantification)
      case σ → τ =>
        Branch(FunctionArrow, List(σ.toAST, τ.toAST))
      case f ₌ τ =>
        Branch(FunctorApplication, List(f.toAST, τ.toAST))
    }
  }

  implicit class ConversionsFromTermToOperator(t: ChurchTerm) {
    def toAST: AST = t.term match {
      case χ(binder) =>
        toAtomic(binder.name)
      case ξ(name) =>
        toAtomic(name)
      case abs @ λ(x, body) =>
        Branch(TermAbstraction,
          List(toAtomic(x.name), (t annotations abs).toAST,
               loop(body)))
      case tabs: Λ =>
        // can't use "unnestBinders" because Λ isn't a binder.
        // maybe we should have some common trait between a binder
        // of bound names and a pseudobinder of free names?
        val (tabses, body) = tabs.detachNestedDoppelgaenger
        Branch(TypeAbstraction,
          List(toParameterList(tabses map (_.alpha.name)),
               loop(body)))

      case ₋(x: λ, xdef) if t.annotations(x) == UnknownType =>
        Branch(LetBinding,
          List(toAtomic(x.name), loop(xdef), loop(x.body)))

      case ₋(f, x) =>
        Branch(TermApplication  , List(loop(f), loop(x)))
      case □(t, τ) =>
        Branch(TypeInstantiation, List(loop(t), τ.toAST))
      case Ξ(t, τ) =>
        Branch(TypeAmnesia      , List(loop(t), τ.toAST))
    }

    private[this]
    def loop(body: Term): AST = ChurchTerm(body, t.annotations).toAST
  }

  private[this] def toAtomic(name: String): AST =
    Leaf(Atomic, Seq(Seq(name)))

  private[this]
  def toParameterList(names: List[String]): AST =
    Branch(TypeParameterList, names map toAtomic)

  private[this]
  def unnestBinders(binder: Type.Binder, binderOp: Operator): AST = {
    val (binders, body) = binder.detachNestedDoppelgaenger
    Branch(binderOp,
      List(toParameterList(binders map (_.name)), body.toAST))
  }

  implicit class ConversionsFromAST(ast: AST) {
    def toProtoChurchTerm: ProtoChurchTerm = ast match {
      case Branch(LetBinding, List(x, xdef, body)) =>
        val t = body.toProtoChurchTerm
        val abs = λ(x.to_ξ)(t.term)
        val ano = UnknownType :: t.annotations
        val dfn = xdef.toProtoChurchTerm
        ProtoChurchTerm(abs ₋ dfn.term, dfn.annotations ++ ano)
      case Branch(TermAbstraction, List(x, xtype, body)) =>
        val t = body.toProtoChurchTerm
        val abs = λ(x.to_ξ)(t.term)
        ProtoChurchTerm(abs, xtype.toType :: t.annotations)
      case Branch(TypeAbstraction,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        val t = body.toProtoChurchTerm
        val parameters = parameterList map (_.to_δ)
        ProtoChurchTerm(Λ(parameters, t.term), t.annotations)
      case Branch(TypeInstantiation, List(term, τ)) =>
        val t = term.toProtoChurchTerm
        ProtoChurchTerm(t.term □ τ.toType, t.annotations)
      case Branch(TypeAmnesia, List(term, τ)) =>
        val t = term.toProtoChurchTerm
        ProtoChurchTerm(t.term Ξ τ.toType, t.annotations)
      case Branch(TermApplication, List(fun, arg)) =>
        val (f, x) = (fun.toProtoChurchTerm, arg.toProtoChurchTerm)
        // annotations are concatenated in reverse preorder
        // (cf. NameBindingLanguage.AST.reverseTraversal)
        ProtoChurchTerm(f.term ₋ x.term, x.annotations ++ f.annotations)
      case Branch(TermParenthetic, List(t)) =>
        t.toProtoChurchTerm
      case x =>
        ProtoChurchTerm(x.to_ξ, Nil)
    }

    def to_ξ: ξ = ast match {
      case Leaf(Atomic, Seq(Seq(name))) =>
        ξ(name)
    }

    def toType: Type = ast match {
      case Branch(UniversalQuantification,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        ∀(parameterList map (_.to_δ), body.toType)
      case Branch(ExistentialQuantification,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        ∃(parameterList map (_.to_δ), body.toType)
      case Branch(FunctionArrow, List(domain, range)) =>
        domain.toType →: range.toType
      case Branch(FunctorApplication, List(functor, arg)) =>
        functor.toType ₌ arg.toType
      case Branch(TypeParenthetic, List(τ)) =>
        τ.toType
      case a =>
        a.to_δ
    }

    def to_δ: δ = ast match {
      case Leaf(Atomic, Seq(Seq(name))) =>
        δ(name)
    }
  }
}

// parse file, produce terms and types
trait Parser extends ParagraphGrammar with ASTConversions with Syntax {
  def parse(s: String): Module =
    parseParagraphs(ParagraphExpr withLines s)

  def parseFile(path: String): Module = {
    val module = parseParagraphs(ParagraphExpr fromFileWithLines path)
    // CAUTION: platform dependence, to rectify when internet is available
    module.filename = path.substring(path.lastIndexOf('/') + 1, path.length)
    module
  }

  def parseParagraphs(paragraphs: Iterator[(AST, Int)]): Module =
    (paragraphs foldLeft Module.empty) {
      case (module, nextParagraph) =>
        processParagraph(nextParagraph, module)
    }

  // starts with an immature module and make it more mature
  def processParagraph(paragraph0: (AST, Int), module: Module): Module = {
    val (paragraph, line) = paragraph0
    paragraph match {
      // the paragraph is a rant, do nothing
      case Leaf(ParagraphComment, _) =>
        module

      // type synonym: add binding now, resolve circularity later
      case Branch(TypeSynonym,
                  List(Branch(TypeParameterList, parameterList), body)) =>
        val lhs :: parameters = parameterList map (_.to_δ)
        val rhs = ∀(parameters, body.toType)
        module addSynonym (lhs, rhs, line)

      // type signature: add binding now, instantiate later
      case Branch(TypeSignature, List(x, xtype)) =>
        val xi = x.to_ξ
        if (module.definitions contains xi)
          sys error s"signature of $x after definition"
        module addSignature (xi, xtype.toType, line)

      // term definition: add binding now, verify type later
      case Branch(TermDefinition, List(x, xdef)) =>
        module.addDefinition(
          x.to_ξ,
          xdef.toProtoChurchTerm.toChurchTerm,
          line
        )

      // typed function definition: requires a signature
      case Branch(TypedFUnctionDefinition,
                  List(Branch(TermParameterList, parameterList), body)) =>
        // do stupid argument extraction for now,
        // do the smart thing after we figure out prenex form
        // (can reuse in ascription, too!)
        val lhs :: parameters = parameterList map (_.to_ξ)
        val τ = module signatures lhs
        val protobody = body.toProtoChurchTerm
        val abs = (parameters foldRight protobody.term)({
           case (x, body) => λ(x)(body)
        }).asInstanceOf[λ]
        val argTypes = (parameters, τ.argumentTypes.toSeq).zipped.map {
          case (_, σ) => σ
        }
        if (argTypes.length != parameters.length)
          sys error (s"too many arguments in the definition of:\n"+
            s"${lhs.name} : ${τ.unparse}")
        val rhs = ProtoChurchTerm(
          abs,
          argTypes ++ protobody.annotations
        ).toChurchTerm
        module addDefinition (
          lhs,
          rhs,
          line
        )
    }
  }

  private[this]
  def getLambdas(t: Term): List[λ] = t match {
    case x @ λ(_, body) => x :: getLambdas(body)
    case ₋(f, x) => getLambdas(f) ++ getLambdas(x)
    case □(t, _) => getLambdas(t)
    case Ξ(t, _) => getLambdas(t)
    case _ => Nil
  }
}
*/
