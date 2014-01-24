// don't set flags here. they're set in Main.scala.
trait Flags {
  private[this] var flag: Set[String] = Set.empty
  def setFlags(_flag: Set[String]) { flag = _flag }

  // trace: don't catch exceptions, I want to see stack traces
  def traceFlag = flag("trace")

  // loop: perform designated task repeatedly for profiling
  def loopFlag = flag("loop")

  // debug: step through constraint resolution on type error
  private[this] def debug = "debug"
  def debugFlag: Boolean = flag(debug)
  def debugFlag_=(_debug: Boolean): Unit =
    if (_debug) flag = flag + debug
    else        flag = flag - debug

  // recurse: permit recursion (causes inf loop in type checker now)
  def recurseFlag: Boolean = flag("recurse")

  // dont-recurse: forbid recursion
  def dontRecurseFlag: Boolean = ! recurseFlag
}
