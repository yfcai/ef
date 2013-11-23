// For Parsers
import scala.util.parsing.combinator._
import scala.util.matching.Regex

trait Parsing extends SystemMF with Pretty with RegexParsers {
  object parse extends Parser {
    def apply(input: String) = {
      name.reset
      useParser(topLevel)(input)
    }
  }

  object parseType extends Parser {
    def apply(input: String) = useParser(typeExpr)(input)
  }

  trait Parser extends RegexParsers {

    // LEXEMES

    val leftP  = """\(""".r
    val rightP = """\)""".r
    val forall = "[∀]".r
    val lambda = "[λ]".r
    val dot    = "[.]".r
    val colon  = "[:]".r
    val arrow  = "[→]".r
    val nil    = "".r
    val ident  = """[^()\[\]{}",'`;#|\\∀λ→ \r\t\f\n]+""".r
    val param  = """[^()\[\]{}",'`;#|\\∀λ→ \r\t\f\n.]+""".r

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
        case _ ~ paramList ~ _ ~ bodyType => ∀(paramList: _*)(bodyType)
      }

    lazy val typeParamList: Parser[List[String]] =
      opList(nil, param ^^ identity[String])

    lazy val funType: Parser[Type] = opList(arrow, belowFun) ^^ {
      _.foldRight[Type](ZeroInfo) { (domain, range) => range match {
        case ZeroInfo  => domain
        case otherwise => domain →: range
      }}
    }

    lazy val typeApp: Parser[Type] = opList(nil, belowTypeApp) ^^ {
      _.foldLeft[Type](ZeroInfo) { (typeFun, typeArg) => typeFun match {
        case ZeroInfo  => typeArg
        case otherwise => ★(typeFun, typeArg)
      }}
    }

    lazy val typeVar: Parser[Type] = ident ^^ { s => α(s) }

    lazy val parenType: Parser[Type] = paren(typeExpr)

    // TERM PARSERS

    lazy val topLevel: Parser[SMFTerm] = termExpr ^^ {
      case SMF(t, _Γ, names) => SMFTerm(t, _Γ, names)
    }

    lazy val termExpr: Parser[SMF] = abs      | belowAbs
    lazy val belowAbs: Parser[SMF] = app      | belowApp
    lazy val belowApp: Parser[SMF] = variable | parenTerm

    lazy val abs: Parser[SMF] = stupidParser

    lazy val app: Parser[SMF] = stupidParser

    lazy val variable: Parser[SMF] = ident ^^ { s => SMF(χ(s), ∅, ∅) }

    lazy val parenTerm: Parser[SMF] = paren(termExpr)

    lazy val stupidParser: Parser[SMF] =
      "there's a pain that can't be spoken".r ^^ {
        _ => sys error "there's a grief that goes on and on"
      }

    // INTERNAL STUFF

    // finite version of SMFTerm
    case class SMF(t : Term, Γ : Map[Name, Type], nameScheme: Map[Name, Name])

    val name = new GenerativeNameGenerator

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

    def ∅[K, V] = Map.empty[K, V]

    case object ZeroInfo extends Type

    def opList[T](operator: Regex, operand: Parser[T]): Parser[List[T]] =
      operand ~ (operator ~> operand).+ ^^ {
        case operand ~ others => operand :: others
      }

    def paren[T](innard: Parser[T]): Parser[T] =
      leftP ~> innard <~ rightP
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
    val t = parse(s).get
    println(t)
    println(pretty(t.t))
    println
  }

  def main(args: Array[String]) {
    τ("α")
    τ("α → β → γ")
    τ("∀α β γ. α → (β → γ) → ((δ → ε) → η) → ζ")
    τ("∀α β. (α → β) → List α → List β")

    t("x")
  }
}
