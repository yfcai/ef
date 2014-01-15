// parse file, produce AST
trait Modules extends Prenex with Nondeterminism {

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

  lazy val _postulates = postulates[Seq[Token]](Nil)

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

    // SYNONYM RESOLUTION

    def resolve(τ: Tree): Tree = resolveBy(typeLexicon, τ)

    def resolveBy(word: String, meaning: Tree, τ: Tree): Tree =
      resolveBy(Map(word -> meaning), τ)

    def resolveBy(lexicon: Map[String, Tree], τ: Tree): Tree =
      τ.fold[Tree] {
        case ∙:(FreeTypeVar, α: String) if lexicon contains α =>
          lexicon(α)
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

    // TYPE INFERENCE

    // low level type inference
    def infer(term: Tree, tape: Tape, toks: Seq[Token]):
        Domain[Seq[Token]] =
      infer(
        term,
        resolvedSignatures.map(p =>
          p._1 -> inject[Seq[Token]](Nil, Success(p._2))),
        tape, toks.head, TokenTracker(toks.tail))

    // CAUTION: don't forget the postulates here!
    def infer(
      term: Tree, Γ: Map[String, Domain[Seq[Token]]],
      tape: Tape, tok: Token, toks: TokenTracker):
        Domain[Seq[Token]] = term match {

      // TAUT
      case χ(x) =>
        Γ.orElse(_postulates).
          orElse[String, Domain[Seq[Token]]]({
          case _ => inject(tok +: toks, Failure("unknown object"))
        })(x)


      // CAUTION: Binders!
      //
      // Binders are tricky because they possess annotations of
      // unknown genera and can change the context Γ. To handle
      // a binder, we need 2 cases. 1 to handle their annotations,
      // 1 to handle themselves & skip over the bound string literal.

      // λ: type annotations
      case τ if τ.tag == Type =>
        // call toks.next a suitable number of times
        τ.preorder.toStream.tail.foreach { _ => toks.next }
        inject[Seq[Token]](Nil, Success(resolve(τ)))

      // λ: skip bound name, context update etc.
      case λ(x, annotation, body) =>
        val mytoks = tok +: toks // extract my tokens before it's too late
        toks.next // skip "x"
        val σ = infer(annotation, Γ, tape, toks.next, toks)
        val τ = infer(body, Γ.updated(x, σ), tape, toks.next, toks)
        inferType(⊹:(AnnotatedAbstraction, σ, τ))(tape)(mytoks)

      // TODO (for Continuation Calculus):
      // handle Λ here.
      case ∙(tag, _) =>
        sys error s"unhandled terminal tag $tag"
      case ⊹(tag: Binder, _*) =>
        sys error s"unhandled binder $tag"

      case ⊹(tag, children @ _*) if ! tag.isInstanceOf[Binder] =>
        val mytoks = tok +: toks
        val types = children.map(t => infer(t, Γ, tape, toks.next, toks))
        inferType(⊹:(tag, types: _*))(tape)(mytoks)
    }


    // high level type error report
    def typeError: Option[Problem] = {
      dfn.foreach { case (name, term) =>
        val toks = dfntoks(name)
        if (! sig.contains(name))
          Some(Problem(toks.head, "definition lacks type signature"))
        val expected = sig(name)
        val expectedType = Prenex(resolve(expected)).normalize

        // TODO: swap in the prefix skipping tape when it's done
        val tape = Nondeterministic.tape

        // find the first type error amongst those that happen
        // at the latest stage of type checking.
        var typeError: Problem = null
        var remainingToks: Int = Int.MaxValue

        val result = tape.find { tape =>
          infer(term, tape, toks).get match {
            case (_, Success(τ0)) =>
              val τ = Prenex(τ0).normalize
              val correct = expectedType α_equiv τ
              if (correct)
                true
              else {
                typeError = Problem(toks.head,
                  s"""|expect $expected
                      |actual $τ
                      |""".stripMargin)
                // whole definition's scanned without freak-outs
                remainingToks = 0
                false
              }
            case (toks, Failure(msg)) =>
              typeError = Problem(toks.head, msg)
              remainingToks = toks.tail.length
              false
          }
        }
        if (result == None)
          return Some(typeError)
      }
      // no definitions suffer from type error
      return None
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
