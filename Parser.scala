import scala.util.parsing.combinator._
import scala.util.matching.Regex

trait Parsing extends SystemMF with Pretty with RegexParsers {
  object parseTerm extends Parser {
    def apply(input: String) = {
      useParser(nakedTermExpr)(input)
    }
  }

  object parseType extends Parser {
    def apply(input: String) = useParser(typeExpr)(input)
  }

  trait Parser extends RegexParsers {

    // LEXEMES

    val leftP  = """\(""".r
    val rightP = """\)""".r
    val leftB  = """\[""".r
    val rightB = """\]""".r
    val forall = "[∀]".r
    val lambda = "[λ]".r
    val LAMBDA = "[Λ]".r
    val dot    = "[.]".r
    val colon  = "[:]".r
    val arrow  = "[→]".r
    val nil    = "".r
    val ident  = """[^()\[\]{}",'`;#|\\∀λΛ→ \r\t\f\n.]+""".r
    val phase  = """([^\n]|\n[^\n])+""".r // delimited by blank line
    val equals = "=".r
    val pstlt  = "postulate".r
    val talias = "type".r
    val tdecl  = "data".r

    // MODULE PARSERS

    def module(literals: PartialFunction[Name, Type]):
        Parser[List[Expr]] = {
      var result: List[Expr] = Nil
      var Γ : Map[Name, Type] = Map.empty
      var aliases = collection.mutable.Seq.empty[(Name, Type)]
      val decls   = collection.mutable.Set.empty[Name]
      def smf2term(smf: SMF) = {
        val context: Map[Name, Type] = (Γ ++ smf.Γ) map {
          case (name, τ) =>
            (name, τ substitute (aliases: _*))
        }
        SMFTerm(smf.t, context orElse literals,
                Set.empty[Name] ++ decls, smf.n)
      }
      paragraph.* ^^ { paragraphs =>
        paragraphs foreach { _ match {
          case Postulate(name, τ) =>
            if (Γ contains name) sys error (
              s"postulate duplicates existing name: $name : $τ"
            )
            Γ = Γ.updated(name, (τ substitute (aliases: _*)).quantifyMinimally)

          case Definition(name, smf) =>
            if (Γ contains name) sys error (
                s"definition duplicates existing name: $name = ${smf.t}"
            )
            require((smf.Γ.keySet & Γ.keySet).isEmpty)
            val term = smf2term(smf)
            Γ = Γ.updated(name, term.getType)
            result = DefExpr(name, term) :: result

          case NakedParagraph(smf) =>
            result = NakedExpr(smf2term(smf)) :: result

          case TypeAlias(name, τ) =>
            aliases = aliases :+ ((name, τ substitute (aliases: _*)))

          case TypeDeclaration(name) =>
            decls += name
        }}
        result.reverse
      }
    }

    lazy val paragraph: Parser[Paragraph] =
      phase ^^ { s =>
        useParser( typeAlias
                 | typeDeclaration
                 | postulate
                 | definition
                 | nakedTopLevelExpr
                 )(s).get
      }

    lazy val typeAlias: Parser[Paragraph] =
      talias ~ ident ~ equals ~ typeExpr ^^ {
        case _ ~ alpha ~ _ ~ τ => TypeAlias(alpha, τ)
      }

    lazy val typeDeclaration: Parser[Paragraph] =
      tdecl ~> ident ^^ (x => TypeDeclaration(x))

    lazy val postulate: Parser[Paragraph] =
      pstlt ~ ident ~ colon ~ typeExpr ^^ {
        case _ ~ name ~ _ ~ τ => Postulate(name, τ)
      }

    lazy val definition: Parser[Paragraph] = {
      name.reset
      ident ~ equals ~ termExpr ^^ {
        case name ~ _ ~ smf => Definition(name, smf)
      }
    }

    lazy val nakedTopLevelExpr: Parser[Paragraph] = {
      name.reset
      termExpr ^^ NakedParagraph
    }

    // TYPE PARSERS

    // parsers combined by | should go from lower to higher precedence
    // lowerType has the highest precedence
    lazy val typeExpr    : Parser[Type] = forallType | belowForall
    lazy val belowForall : Parser[Type] = funType    | belowFun
    lazy val belowFun    : Parser[Type] = typeApp    | belowTypeApp
    lazy val belowTypeApp: Parser[Type] = typeVar    | parenType

    lazy val forallType: Parser[Type] =
      // ~> <~ cause problems here, no idea why
      forall ~ typeParamList ~ dot ~ typeExpr ^^ {
        case _ ~ paramList ~ _ ~ body => ∀(paramList: _*)(body)
      }

    lazy val typeParamList: Parser[List[String]] =
      opList(nil, ident ^^ identity[String]) |
                 (ident ^^ {x => List(x: String)})

    lazy val funType: Parser[Type] = opList(arrow, belowFun) ^^ {
      _.foldRight[Type](ZeroInfo) { (domain, range) =>
        if (ZeroInfo == range) domain
        else                   domain →: range
      }
    }

    lazy val typeApp: Parser[Type] = opList(nil, belowTypeApp) ^^ {
      _.foldLeft[Type](ZeroInfo) { (typeFun, typeArg) =>
        if (ZeroInfo == typeFun) typeArg
        else                     ★(typeFun, typeArg)
      }
    }

    lazy val typeVar: Parser[Type] = ident ^^ { s => α(s) }

    lazy val parenType: Parser[Type] = paren(typeExpr)

    // TERM PARSERS

    lazy val nakedTermExpr: Parser[SMFTerm] = {
      name.reset
      termExpr ^^ {
        case SMF(t, _Γ, names) => SMFTerm(t, _Γ, Set.empty, names)
      }
    }

    lazy val termExpr: Parser[SMF] = abs      | belowAbs
    lazy val belowAbs: Parser[SMF] = app      | belowApp
    lazy val belowApp: Parser[SMF] = variable | parenTerm

    lazy val abs: Parser[SMF] =
      lambda ~ termParam ~ dot ~ termExpr ^^ {
        case _ ~ ((pName, pType)) ~ _ ~ body =>
          val id = name.next
          SMF(
            λ(id, body.t rename (pName -> id)),
            body.Γ.updated(id, pType),
            body.n.updated(id, pName)
          )
      }

    lazy val termParam: Parser[(String, Type)] =
      ident ~ colon ~ typeExpr ^^ {
        case pName ~ _ ~ pType => (pName, pType)
      }

    lazy val app: Parser[SMF] = opList(nil, belowApp) ^^ {
      _.foldLeft[SMF](ZeroInfo) { (f, x) =>
        if (ZeroInfo == f)
          x
        else {
          assert((f.Γ.keySet & x.Γ.keySet).isEmpty)
          assert((f.n.keySet & x.n.keySet).isEmpty)
          SMF(ε(f.t, x.t), f.Γ ++ x.Γ, f.n ++ x.n)
        }
      }
    }

    lazy val variable: Parser[SMF] = ident ^^ { s => SMF(χ(s), ∅, ∅) }

    lazy val parenTerm: Parser[SMF] = paren(termExpr)

    // INTERNAL STUFF

    // internal parsers

    def opList[T](operator: Regex, operand: Parser[T]): Parser[List[T]] =
      operand ~ (operator ~> operand).+ ^^ {
        case operand ~ others => operand :: others
      }

    def paren[T](innard: Parser[T]): Parser[T] =
      leftP ~> innard <~ rightP

    // name generation
    private[this] case class ID(index: Int) extends SecretLocalName
    val name = new GenerativeNameGenerator(ID)

    // finite version of SMFTerm
    case class SMF(t : Term, Γ : Map[Name, Type], n: Map[Name, Name])
    object ZeroInfo extends SMF(ZeroInfoTerm, ∅, ∅) with Type
    case object ZeroInfoTerm extends Term

    def ∅[K, V] = Map.empty[K, V]

    // data structure for file parsing

    /** Result of parsing a module */
    trait Expr

    /** Result of parsing a paragraph */
    sealed trait Paragraph

    case class DefExpr(name: Name, term: SMFTerm) extends Expr
    case class NakedExpr(get: SMFTerm) extends Expr

    case class Definition(name: String, smf: SMF) extends Paragraph
    case class Postulate(name: String, τ : Type) extends Paragraph
    case class NakedParagraph(smf: SMF) extends Paragraph
    case class TypeAlias(alpha: Name, τ : Type) extends Paragraph
    case class TypeDeclaration(alpha: Name) extends Paragraph



    // result data struct
    sealed trait Result[T] { def get: T }
    case class OK[T](get: T) extends Result[T]
    case class KO[T](msg: String) extends Result[T] {
      override def get: T = sys error msg
    }
    def useParser[T](parser: Parser[T])(input: String): Result[T] =
      parseAll(parser, input) match {
        case Success(result, _) => OK(result)
        case failure: NoSuccess => KO(failure.msg)
      }
  }
}

// hacked-together System F parser for the demo
trait ParsingF extends Parsing with PrettyF with RenamingF {
  import SystemF._

  trait ParserF extends Parser {
    override
    lazy val belowAbs: Parser[SMF] = typeAbstraction | belowAbsT

    lazy val belowAbsT: Parser[SMF] = app | belowApp

    // override old abs by a body that's different only after
    // implicits are resolved
    override
    lazy val abs: Parser[SMF] =
      lambda ~ termParam ~ dot ~ termExpr ^^ {
        case _ ~ ((pName, pType)) ~ _ ~ body =>
          val id = name.next
          SMF(
            λ(id, body.t rename (pName -> id)),
            body.Γ.updated(id, pType),
            body.n.updated(id, pName)
          )
      }

    lazy val typeAbstraction: Parser[SMF] =
      LAMBDA ~ typeParamList ~ dot ~ termExpr ^^ {
        case _ ~ params ~ _ ~ body =>
          SMF(
            Λ(params map {alpha => alpha: Name})(body.t),
            body.Γ,
            body.n
          )
      }

    override
    lazy val app: Parser[SMF] = opList(nil, typeArg | belowApp) ^^ {
      _.foldLeft[SMF](ZeroInfo) { (f, x) =>
        if (ZeroInfo == f)
          x
        else {
          assert((f.Γ.keySet & x.Γ.keySet).isEmpty)
          assert((f.n.keySet & x.n.keySet).isEmpty)
          x.t match {
            case TypeApp(typeArg) =>
              SMF(f.t □ typeArg, f.Γ, f.n)

            case _ =>
              SMF(ε(f.t, x.t), f.Γ ++ x.Γ, f.n ++ x.n)
          }
        }
      }
    }

    // hack
    lazy val typeArg: Parser[SMF] =
      leftB ~> typeExpr <~ rightB ^^ {
        case typeArg =>
          SMF(TypeApp(typeArg), Map.empty, Map.empty)
      }

    case class TypeApp(τ : Type) extends Term

    case class DefExprF(name: Name, term: FTerm) extends Expr
    case class NakedExprF(get: FTerm) extends Expr

    // a copy of super.module
    override
    def module(literals: PartialFunction[Name, Type]):
        Parser[List[Expr]] = {
      var result: List[Expr] = Nil
      var Γ : Map[Name, Type] = Map.empty
      var aliases = collection.mutable.Seq.empty[(Name, Type)]
      val decls   = collection.mutable.Set.empty[Name]
      def smf2term(smf: SMF) = {
        val context: Map[Name, Type] = (Γ ++ smf.Γ) map {
          case (name, τ) =>
            (name, τ substitute (aliases: _*))
        }
        FTerm(smf.t, context orElse literals, smf.n)
      }
      paragraph.* ^^ { paragraphs =>
        paragraphs foreach { _ match {
          case Postulate(name, τ) =>
            if (Γ contains name) sys error (
              s"postulate duplicates existing name: $name : $τ"
            )
            Γ = Γ.updated(name, τ substitute (aliases: _*))

          case Definition(name, smf) =>
            if (Γ contains name) sys error (
                s"definition duplicates existing name: $name = ${smf.t}"
            )
            require((smf.Γ.keySet & Γ.keySet).isEmpty)
            val term = smf2term(smf)
            Γ = Γ.updated(name, term.getType)
            result = DefExprF(name, term) :: result

          case NakedParagraph(smf) =>
            result = NakedExprF(smf2term(smf)) :: result

          case TypeAlias(name, τ) =>
            aliases = aliases :+ ((name, τ substitute (aliases: _*)))

          case TypeDeclaration(name) =>
            decls += name
        }}
        result.reverse
      }
    }
  }
}


trait DecimalLiterals extends FreshNames with Types {
  final val decimalLiteral: PartialFunction[Name, Type] = {
    case StringLiteral(s) if s matches "(-)?[0-9]+" => "ℤ"
  }
}

trait DecimalModuleParser extends Parsing with DecimalLiterals {
  object parseModule extends Parser {
    lazy val moduleParser = module(decimalLiteral)

    def apply(content: String): List[Expr] =
      useParser(moduleParser)(content).get
  }

  type Expr      = parseModule.Expr
  type DefExpr   = parseModule.DefExpr
  val  DefExpr   = parseModule.DefExpr
  type NakedExpr = parseModule.NakedExpr
  val  NakedExpr = parseModule.NakedExpr
}

trait FileParser extends DecimalModuleParser {
  def process(result: List[Expr]): Unit

  def main(args: Array[String]) {
    val content: String = try {
      val Array(filename) = args
      val source = scala.io.Source.fromFile(filename)
      val content = source.getLines mkString "\n"
      source.close()
      content
    }
    catch { case e: Throwable =>
      Console.err.println(
        """|Usage: <this-command> <one-single-file>
           |""".stripMargin)
      sys exit -1
    }

    process(parseModule(content))
  }
}

object TestParser extends Parsing {
  def τ(s : String) {
    val τ = parseType(s).get
    println(τ)
    println(pretty(τ))
    println
  }

  def t(s : String) {
    val t = parseTerm(s).get
    println(t)
    println(pretty(t.getTerm))
    println
  }

  val Y = """|λ f : (α → α) → (α → α) .
             |  (λ x : ∀ β . β → α → α . f (x x))
             |  (λ x : ∀ β . β → α → α . f (x x))
             |""".stripMargin // is ill-typed

  def main(args: Array[String]) {
    τ("α")
    τ("∀ α . α → β → γ")
    τ("∀ α β γ . α → (β → γ) → ((δ → ε) → η) → ζ")
    τ("∀α β. (α → β) → List α → List β")

    t("λ f : α → β → γ . f (g x) (h y)")
    t("λ x : ∀ β . β → α → α . f (x x)")
    t(Y)
  }
}
