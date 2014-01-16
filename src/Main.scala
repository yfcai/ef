object Main extends ARGV0 with Calculi {
  def main(args: Array[String]): Unit =
    if (args.isEmpty)
      System.err.println(
        s"""|Usage: THIS-THING COMMAND [FILE...]
            |  where
            |    COMMAND = test | run | type | reduce
            |      where
            |        test   : run experiments to verify sanity
            |        run    : type check files, then execute them
            |        reduce : reduce naked expressions without
            |                 regard for types and print the result
            |""".stripMargin)
    else args.head match {
      case "type"   => TypeChecker.execute(args.tail)
      case "test"   => Experiments.run
      case cmd      => System.err.println(s"unknown command: $cmd")
    }
}

// Based on
// http://designbygravity.wordpress.com/2009/11/04/argv0-for-java/
//
// TODO: read jar's x-bit & manifest to come up with good command
trait ARGV0 {
  import java.io._
  import java.net._

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
