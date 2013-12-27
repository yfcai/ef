trait Compiler extends Parser {
  def processModule(m: Module): Unit

  def main(args: Array[String]): Unit = args match {
    case Array(path) => processModule(parseFile(path))
    case _ => println("usage: <this-command> <one-single-file>")
  }
}

object CheckEF extends Compiler with Gammas {
  def processModule(m: Module) {
    val Γ = Γ_ℤ(m) // type-checked!
    m.definitions.toList.sortBy(x => m lineNumber x._1) foreach {
      case (xi @ ξ(name), c @ ChurchTerm(t, _)) =>
        val τ = m.signatures.withDefault(_ => Γ ⊢ t)(xi)
        println(s"$name : ${τ.unparse}")
        println(s"$name = ${c.unparse}\n")
    }
  }
}
