object Main extends ARGV0 with Calculi {
  def loopSet(flags: Set[String]): Boolean = flags("loop")

  def main(args: Array[String]) {
      val flags = args.takeWhile(_ startsWith "-").map(_.tail)
      val rest = args.drop(flags.length)
      if (rest.isEmpty)
        System.err.print(
          s"""|Usage: $argv0 [-FLAG₁ -FLAG₂ ...] COMMAND [STUFF...]
              |  where
              |    COMMAND = test | run | type | reduce
              |      where
              |        test   : run (optionally named) experiments to
              |                 verify sanity
              |
              |        run    : type check files, then execute them
              |
              |        type   : type check files
              |
              |        reduce : reduce naked expressions without
              |                 regard for types and print the result
              |
              |Flags
              |
              | -debug    step through constraint solver on type error
              |
              | -loop     run designated command repeatedly useful for
              |           useful for profiling
              |
              | -recurse  permits recursion (currently puts type
              |           checker in an infinite loop)
              |
              | -trace    print stack trace on error of any kind
              |""".stripMargin)
      else {
        val (head, tail) = (rest.head, rest.tail)
        val flag = Set(flags: _*)
        val loop = flag("loop")
        do {
          head match {
            case "test"   => Experiments.run(tail, flag("debug"))
            case "run"    => Executioner.execute(tail, flag)
            case "type"   => TypeChecker.execute(tail, flag)
            case "reduce" => Reductionist.execute(tail, flag)
            case cmd      => System.err.println(s"unknown command: $cmd")
          }
        }
        while (loop)
    }
  }
}

// Based on
// http://designbygravity.wordpress.com/2009/11/04/argv0-for-java/
trait ARGV0 {
  import java.io._
  import java.net._

  // placeholder for now due to Java's disregard of C's tradition
  // TODO: read jar's x-bit & manifest to come up with good command
  def argv0: String = "THIS-THING"

  def findRootPath(obj: AnyRef): String = {
    val clazz = obj.getClass
    val url = clazz.getResource(s"${clazz.getSimpleName}.class")
    val homeLocation =
      new File(URLDecoder.decode(url.getPath, "UTF-8")).getParentFile
    val root =
      if (clazz.getPackage != null)
        (0 to clazz.getPackage.getName.count(_ == '.')).
          foldRight(homeLocation)((_, file) => file.getParentFile).
          getPath
      else
        homeLocation.getPath
    val fileColon = "file:"
    val exclamation = "!"
    url.getProtocol match {
      case "file" =>
        assert(root.startsWith(fileColon))
        root.drop(fileColon.length)
      case "jar" =>
        assert(root.startsWith(fileColon))
        assert(root.endsWith(exclamation))
        root.substring(fileColon.length, root.length - exclamation.length)
    }
  }
}
