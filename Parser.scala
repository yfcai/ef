// For Parsers
import scala.util.parsing.combinator._
import scala.util.matching.Regex

trait Parsing extends SystemMF with Pretty with RegexParsers {
  object parseTerm extends Parser {
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
    val ident  = """[^()\[\]{}",'`;#|\\∀λ→ \r\t\f\n.]+""".r

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

    lazy val topLevel: Parser[SMFTerm] = termExpr ^^ {
      case SMF(t, _Γ, names) => SMFTerm(t, _Γ, names)
    }

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
