// For Parsers
import scala.util.parsing.combinator._
import scala.util.matching.Regex

trait Parsing extends SystemMF with Pretty with RegexParsers {
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
    lazy val typeExpr: Parser[Type] =
      forallType | funType | typeApp | lowerType

    lazy val forallType: Parser[Type] =
      // ~> <~ cause problems here, no idea why
      forall ~ typeParamList ~ dot ~ typeExpr ^^ {
        case _ ~ paramList ~ _ ~ bodyType => ∀(paramList: _*)(bodyType)
      }

    lazy val funType: Parser[Type] = opList(arrow, typeApp | lowerType) ^^ {
      _.foldRight[Type](ZeroInfo) { (domain, range) => range match {
        case ZeroInfo  => domain
        case otherwise => domain →: range
      }}
    }

    lazy val typeApp: Parser[Type] = opList(nil, lowerType) ^^ {
      _.foldLeft[Type](ZeroInfo) { (typeFun, typeArg) => typeFun match {
        case ZeroInfo  => typeArg
        case otherwise => ★(typeFun, typeArg)
      }}
    }

    lazy val lowerType: Parser[Type] = typeVar | parenType

    lazy val typeParamList: Parser[List[String]] =
      opList(nil, param ^^ identity[String])

    lazy val typeVar: Parser[Type] = ident ^^ { s => α(s) }

    lazy val parenType: Parser[Type] = paren(typeExpr)

    // TERM PARSERS

    lazy val termExpr: Parser[SMFTerm] = ???

    // INTERNAL STUFF

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

  def main(args: Array[String]) {
    τ("α")
    τ("α → β → γ")
    τ("∀α β γ. α → (β → γ) → ((δ → ε) → η) → ζ")
    τ("∀α β. (α → β) → List α → List β")
  }
}
