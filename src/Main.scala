object Main {
  def loopSet(flags: Set[String]): Boolean = flags("loop")

  def main(args: Array[String]) {
    val flags = args.takeWhile(_ startsWith "-").map(_.tail)
    val tail = args.drop(flags.length)
    SmallStepRepl.setFlags(Set(flags: _*))
    SmallStepRepl.recurseFlag = true
    SmallStepRepl.startRepl(tail)
  }
}
