// For Parsers
import scala.util.parsing.combinator._
import scala.util.matching.Regex

// For REPL
import scala.tools.jline

trait Parser extends TypedTerms with RegexParsers {
}

object TestParser {
  def main(args: Array[String]) {
    println("yo dawg")
  }
}
