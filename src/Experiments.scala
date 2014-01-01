object Experiments {
  val onTrial = ProtoASTExperiment

  val experiments = List(
    ProtoASTExperiment)

  def maintenance() = experiments foreach { ex =>
    if (ex.run != ex.expected)
      sys error s"failed: $ex"
  }

  def main(args: Array[String]) = experiments foreach { experiment =>
    onTrial.trial
    println("MAINTAINING ...")
    maintenance()
    println("MAINTENANCE SUCCESSFUL")
  }
}

trait Experiment {
  def run: String
  def expected: String = "UNEXPECTED"

  def trial(): Unit = print(run)

  def debug(): Unit = {
    val (actual, expect) = (run, expected)
    (actual.lines.toSeq, expect.lines.toSeq).zipped foreach {
      case (lhs, rhs) =>
        println(lhs == rhs)
        println(lhs + "$")
        println(rhs + "$\n")
    }
    println(s"actual length = ${actual.length}")
    println(s"expect length = ${expect.length}")
  }

  val stream = new collection.mutable.StringBuilder

  def puts(s: String) = { put(s) ; stream += '\n' }
  def put(s: String) = stream ++= s

  def dump(): String = {
    val result = stream.toString
    stream.clear()
    result
  }
}

object ProtoASTExperiment extends Experiment with ProtoAST {
  val keywords: Set[String] = Set("(", ")")
  val trees = List(
    "a () (b c (d) ((((e f))) g) h)",
    "((((()))))",
    "()(()())((()())(()()))",
    "((((())))((",
    "(hi hi (hi hi (hi) hi) hi))(hi)")

  case object TopLevel extends UnclassifiedTag

  def run: String = {
    trees foreach { tree =>
      try {
        val t = ⊹(TopLevel, ProtoAST(tokenize(tree)): _*)
        puts(s"${t.print}\n")
      }
      catch {
        case p: Problem =>
          puts(s"${p.getMessage}")
      }
    }
    dump()
  }

  override val expected = """TopLevel
  ∙(TokenAST, 0:a)
  ProtoAST
  ProtoAST
    ∙(TokenAST, 6:b)
    ∙(TokenAST, 8:c)
    ∙(TokenAST, 11:d)
    ProtoAST
      ProtoAST
        ∙(TokenAST, 18:e)
        ∙(TokenAST, 20:f)
      ∙(TokenAST, 25:g)
    ∙(TokenAST, 28:h)

TopLevel
  ProtoAST

TopLevel
  ProtoAST
  ProtoAST
    ProtoAST
    ProtoAST
  ProtoAST
    ProtoAST
      ProtoAST
      ProtoAST
    ProtoAST
      ProtoAST
      ProtoAST

#LINE:1
((((())))((
          ^
expect right parenthesis after this

#LINE:1
(hi hi (hi hi (hi) hi) hi))(hi)
                          ^
unmatched right parenthesis

"""
}
