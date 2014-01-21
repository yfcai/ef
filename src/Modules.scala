// parse file, produce AST
trait Modules extends Syntax {
  case object ParagraphExpr extends TopLevelGenus {
    val ops = List(TypeSynonym, Signature, Definition, NakedExpression)
  }

  case object NakedExpression extends TopLevelGenus {
    val ops = List(Term)

    def unapply(t: Tree): Option[Tree] =
      if (t.tag.genus == Term)
        Some(t)
      else
        None
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

  def ascriptionFailure(expected: Tree, actual: Tree): String =
    s"""|The type
        |
        |  ${actual.unparse}
        |
        |cannot be ascribed to
        |
        |  ${expected.unparse}
        |
        |""".stripMargin


  case class Module
  ( syn    : Map[String, Tree       ] ,
    syntoks: Map[String, List[Token]] ,
    sig    : Map[String, Tree       ] ,
    sigtoks: Map[String, List[Token]] ,
    dfn    : Map[String, Tree       ] ,
    dfntoks: Map[String, List[Token]] ,
    naked  : Seq[(Tree, List[Token])] ) {

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
          dfn, dfntoks,
          naked)
      case Signature(x, τ) =>
        ensureUnique(sig, x, toks.head)
        Module(
          syn, syntoks,
          sig.updated(x, τ), sigtoks.updated(x, toks),
          dfn, dfntoks,
          naked)
      case Definition(x, t) =>
        ensureUnique(dfn, x, toks.head)
        Module(
          syn, syntoks,
          sig, sigtoks,
          dfn.updated(x, t), dfntoks.updated(x, toks),
          naked)
      case NakedExpression(e) =>
        Module(
          syn, syntoks, sig, sigtoks, dfn, dfntoks,
          naked.:+((e, toks)))
      case _ =>
        sys error s"undetected parse error on ${t.tag}:\n${t.unparse}"
    }

    // strip the "LHS" and the "=" away from token stream
    def getRHSTokens(drop: Int)
        (tokens: Map[String, Seq[Token]], name: String):
        Seq[Token] = tokens(name).drop(drop)

    // drop "LHS" & "="
    def getDFNTokens = getRHSTokens(2) _

    // drop all those tokens associated with annotations:
    //
    //  Universal, binder of MyAlias
    //    ∙(LiteralTag(java.lang.String), MyAlias)
    //    Annotation
    //      ∙(Nope, ())
    //      ∙(Nope, ())
    //
    def getSYNTokens = getRHSTokens(5) _

    def sortNames(defs: Map[String, Tree], toks: Map[String, Seq[Token]]):
        List[String] =
      defs.keys.toList.sortBy(key => toks(key).head.line)
  }

  object Module {
    val empty: Module =
      Module(Map.empty, Map.empty, Map.empty,
             Map.empty, Map.empty, Map.empty,
             Seq.empty)

    def apply(source: String): Module =
      fromParagraphs(Paragraphs(source))

    def fromFile(file: String): Module =
      fromParagraphs(Paragraphs.fromFile(file))

    def fromParagraphs(paragraphs: Iterator[Paragraph]): Module =
      paragraphs.foldLeft(empty) {
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

// synonym resolution
trait Aliasing extends Modules {
  def globalTypes: PartialFunction[String, Tree]
  def globalTerms: PartialFunction[String, Tree]

  implicit class SynonymResolution(val module: Module) {
    import module._

    // SYNONYM RESOLUTION

    def resolve(τ: Tree): Tree = resolveBy(typeLexicon, τ)

    def resolveBy(word: String, meaning: Tree, τ: Tree): Tree =
      resolveBy(Map(word -> meaning), τ)

    def resolveBy(lexicon: Map[String, Tree], τ: Tree): Tree =
      τ.fold[Tree] {
        case ∙:(FreeTypeVar, α: String) if lexicon contains α =>
          lexicon(α)
        case ∙:(FreeTypeVar, α: String) if globalTypes isDefinedAt α =>
          globalTypes(α)
        case ⊹:(TypeApplication,
               universal @ ⊹(Universal, _, Annotation.none(), _),
               σ) =>
          universal(σ)
        case otherwise =>
          Tree(otherwise)
      }

    lazy val typeLexicon: Map[String, Tree] =
      syn.foldRight(Map.empty[String, Tree]) {
        case ((word, definition), lexicon) =>
          val meaning = resolveBy(lexicon, definition)
          lexicon.map({
            case (key, value) =>
              (key, resolveBy(word, meaning, value))
          }).updated(word, meaning)
      }

    lazy val resolvedSignatures: Map[String, Tree] =
      sig.map(p => (p._1, resolve(p._2)))

    // USEFUL THINGS INDEPENDENT OF COMPOSITIONAL TYPING

    def isGlobalType(α: String): Boolean = globalTypes.isDefinedAt(α)
    def isGlobalTerm(x: String): Boolean = globalTerms.isDefinedAt(x)

    // find out undefined type names (only possible error in synonyms)
    def discoverUnknownInTypes: Option[Problem] = {
      sortNames(syn, syntoks).foreach { typeName =>
        val typeDef = syn(typeName)
        val τ = resolve(æ(typeName))
        (typeDef.preorder.toSeq, getSYNTokens(syntoks, typeName)).
          zipped.foreach {
            case (æ(x), tok)
                if ! syn.contains(x) && ! isGlobalType(x) =>
              return Some(Problem(tok, s"unknown type $x"))
            case _ =>
              ()
          }
      }
      None
    }

    // mostly duplicated code...
    def discoverUnknownInTerms: Option[Problem] = {
      sortNames(dfn, dfntoks).foreach { termName =>
        val t = dfn(termName)
        (t.preorder.toSeq, getDFNTokens(dfntoks, termName)).zipped.foreach {
          case (χ(x), tok)
              if ! sig.contains(x) && ! isGlobalTerm(x) =>
            return Some(Problem(tok, s"unknown term $x"))
          // if an unknown type happens in an annotation,
          // then it will be quantified over.
          case _ =>
            ()
        }
      }
      None
    }

    def discoverUnsignedDefinitions: Option[Problem] = {
      sortNames(dfn, dfntoks).foreach { x =>
        if (! sig.contains(x))
          return Some(Problem(dfntoks(x).head,
            "definition lacks type signature"))
      }
      None
    }
  }
}

trait TypedModules extends Modules {
  def typeCheck(m: Module): Either[Problem, Seq[(Tree, Tree, Token)]]
}

trait CompositionallyTypeableModules
    extends TypedModules with Aliasing
       with Prenex with Nondeterminism
{
  def typeCheck(m: Module): Either[Problem, Seq[(Tree, Tree, Token)]] =
    new TypingModules(m).typeCheck

  // ensure correct tracking of tokens
  case class TokenTracker(var tokens: Seq[Token]) {
    def next: Token = {
      val tok = tokens.head
      tokens = tokens.tail
      tok
    }

    def remaining: Int = tokens.length

    def +: (tok: Token): Seq[Token] = tok +: tokens
  }

  // to be extended by type-system-specific subclasses
  trait Domain[S] {
    def get: (S, Status[Tree])
  }

  def inject[T](payload: T, τ: Status[Tree]): Domain[T]
  def postulates[T]: T => PartialFunction[String, Domain[T]]
  def inferType[T]: PartialFunction[TreeF[Domain[T]],
    Tape => T => Domain[T]]

  def mayAscribe(from: Tree, to: Tree): Boolean


  implicit class TypingModules(module0: Module)
      extends SynonymResolution(module0)
  {
    import module0._

    // TYPE INFERENCE

    // low level type inference
    def infer(term: Tree, tape: Tape, toks: Seq[Token]):
        Domain[Seq[Token]] =
      infer(
        term,
        resolvedSignatures.map(p =>
          p._1 -> inject[Seq[Token]](Nil, Success(p._2))),
        postulates[Seq[Token]](Nil),
        tape, toks.head, TokenTracker(toks.tail))

    // CAUTION: don't forget the postulates here!
    def infer(
      term: Tree,
      Γ: Map[String, Domain[Seq[Token]]],
      globals: PartialFunction[String, Domain[Seq[Token]]],
      tape: Tape, tok: Token, toks: TokenTracker):
        Domain[Seq[Token]] = term match {

      // TAUT
      case χ(x) =>
        Γ.orElse(globals).orElse[String, Domain[Seq[Token]]]({
          case _ => inject(tok +: toks, Failure("unknown object"))
        })(x)


      // CAUTION: Binders!
      //
      // Binders are tricky because they possess annotations of
      // unknown genera and can change the context Γ. To handle
      // a binder, we need 2 cases. 1 to handle their annotations,
      // 1 to handle themselves & skip over the bound string literal.

      // λ: type annotations
      case τ if τ.tag.genus == Type =>
        // call toks.next a suitable number of times
        τ.preorder.toStream.tail.foreach { _ => toks.next }
        inject[Seq[Token]](Nil, Success(resolve(τ)))

      // λ: skip bound name, context update etc.
      case λ(x, annotation, body) =>
        val mytoks = tok +: toks // extract my tokens before it's too late
        toks.next // skip "x"
        val σ = infer(annotation, Γ, globals, tape, toks.next, toks)
        val τ = infer(body, Γ.updated(x, σ), globals, tape, toks.next, toks)
        inferType(⊹:(AnnotatedAbstraction, σ, τ))(tape)(mytoks)

      // TODO (for Continuation Calculus):
      // handle Λ here.
      case terminal @ ∙(tag, _) =>
        sys error s"unhandled terminal $terminal"
      case ⊹(tag: Binder, _*) =>
        sys error s"unhandled binder $tag"

      case ⊹(tag, children @ _*) if ! tag.isInstanceOf[Binder] =>
        val mytoks = tok +: toks
        val types = children.map(t =>
          infer(t, Γ, globals, tape, toks.next, toks))
        inferType(⊹:(tag, types: _*))(tape)(mytoks)
    }

    def findFirstType(term: Tree, toks: Seq[Token],
      predicate: Tree => Boolean = _ => true,
      errorMessage: Tree => String = _ => "predicate unsatisfied"):
        Either[Problem, Tree] = {

      // TODO: swap in the prefix skipping tape when it's done
      val tape = Nondeterministic.tape

      // find the first type error amongst those that happen
      // at the latest stage of type checking.
      var typeError: Problem = null
      var remainingToks: Int = Int.MaxValue

      def assignError(err: => Problem, len: Int): Unit =
        if (len < remainingToks) {
          remainingToks = len
          typeError = err
        }

      tape.toStream.findFirst[Tree] { tape =>
        infer(term, tape, toks).get match {
          case (_, Success(τ)) =>
            if (predicate(τ))
              Some(τ)
            else {
              assignError(Problem(toks.head, errorMessage(τ)), 0)
              None
            }
          case (toks, Failure(msg)) =>
            assignError(Problem(toks.head, msg), toks.tail.length)
            None
        }
      } match {
        case None => Left(typeError)
        case Some(τ) => Right(τ)
      }
    }

    // high level type error report
    def typeErrorInDefinitions: Option[Problem] =
      discoverUnknownInTypes.fold[Option[Problem]] {
        val names = sortNames(dfn, dfntoks)
        names.find(x => ! sig.contains(x)).fold[Option[Problem]] {
          names.foreach { name =>
            val term = dfn(name)
            val toks = getDFNTokens(dfntoks, name)
            val expected = sig(name)
            val expectedType = Prenex(resolve(expected)).normalize

            findFirstType(
              term,
              toks,
              τ => mayAscribe(Prenex(τ).normalize, expectedType),
              τ => ascriptionFailure(expected, τ)) match {
              case Left(typeError) =>
                return Some(typeError)
              case Right(_) =>
                ()
            }
          } ; None
        } {
          name => Some(Problem(
            // can't use toks.head: LHS's already dropped
            dfntoks(name).head,
            "definition lacks type signature"))
        }
      } {
        Some.apply
      }

    // assume definitions are fine, check naked expressions
    def typeNakedExpressions: Either[Problem, Seq[(Tree, Tree, Token)]] =
      Right(naked.map { case (t, toks) =>
        findFirstType(t, toks) match {
          case Left(problem) =>
            return Left(problem)
          case Right(τ) =>
            (t, τ, toks.head)
        }
      })

    /** @return either a problem or a sequence of naked
      *         top-level expressions with their types
      */
    def typeCheck: Either[Problem, Seq[(Tree, Tree, Token)]] =
      typeErrorInDefinitions.fold(typeNakedExpressions)(Left.apply)
  }
}
