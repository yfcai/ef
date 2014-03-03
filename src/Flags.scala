// don't set flags here. they're set in Main.scala.
trait Flags {
  private var flag: Set[String] = Set.empty
  def setFlags(_flag: Set[String]) { flag = _flag }
  def getFlags: Set[String] = flag

  def copyFlags(x: Flags): Unit = flag = x.flag

  def setFlag(flagName: String, set: Boolean): Unit =
    if (set) flag = flag + flagName
    else     flag = flag - flagName

  // trace: don't catch exceptions, I want to see stack traces
  def traceFlag = flag("trace")

  // loop: perform designated task repeatedly for profiling
  def loopFlag = flag("loop")

  // debug: step through constraint resolution on type error
  private[this] def debug = "debug"
  def debugFlag: Boolean = flag(debug)
  def debugFlag_=(set: Boolean) = setFlag(debug, set)

  // recurse: permit recursion (causes inf loop in type checker now)
  private[this] def recurse = "recurse"
  def recurseFlag: Boolean = flag(recurse)
  def recurseFlag_=(set: Boolean) = setFlag(recurse, set)

  // dont-recurse: forbid recursion
  def dontRecurseFlag: Boolean = ! recurseFlag

  // ascii: do not print unicode characters
  def asciiFlag: Boolean = flag("ascii")

  // unicode: print unicode (overrides ascii)
  private[this] def unicode = "unicode"
  def unicodeFlag: Boolean = flag(unicode)
  def unicodeFlag_=(set: Boolean) = setFlag(unicode, set)

  // O WINDOWS...
  val I_am_Windows =
    if (System.getProperty("os.name").toLowerCase startsWith "win")
      true
    else
      false

  def I_hate_unicode =
    ! unicodeFlag & (I_am_Windows | asciiFlag)

  // whether to insert polymorphism marker everywhere
  def absoluteFlag: Boolean = flag("absolute")
}
