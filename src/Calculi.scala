trait Calculi {
  object ExistentialFCalculus extends ExistentialF

  trait Executable {
    def execute(args: Array[String]): Unit

    def err(s: Any) = System.err.println(s.toString)
    def print(s: Any) = { System.out.print(s) ; System.out.flush() }
  }

  object TypeChecker extends Executable {
    def execute(args: Array[String]): Unit = args.foreach { file =>
      val extension = file.substring(file.lastIndexOf(".") + 1)
      val calculus: Modules = extension match {
        case "ef" => ExistentialFCalculus
        case _ =>
          err(s"$file: unknown extension")
          return
      }
      try {
        val module = calculus.Module.fromFile(file)
        println(s"Checking $file")
        module.typeErrorInDefinitions match {
          case None =>
            println(s"$file is well-typed.")
          case Some(problem) =>
            err(problem.getMessage)
            return
        }
        // TODO: type naked expressions
      } catch {
        case e: java.io.FileNotFoundException =>
          err(s"$file: not found")
          return
      }
    }
  }
}
