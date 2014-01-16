trait Calculi {
  type Calculus = Modules

  object ExistentialFCalculus extends ExistentialF

  trait Executable {
    def execute(args: Array[String]): Unit

    def err(s: Any) = System.err.println(s.toString)
    def print(s: Any) = { System.out.print(s) ; System.out.flush() }
  }

  object TypeChecker extends Executable {
    def execute(args: Array[String]): Unit = args.foreach { file =>
      val extension = file.substring(file.lastIndexOf(".") + 1)
      val calculus: Calculus = extension match {
        case "ef" => ExistentialFCalculus
        case _ =>
          err(s"$file: unknown extension")
          return
      }
      try {
        val module = calculus.Module.fromFile(file)
        module.typeCheck match {
          case Left(problem) =>
            err(problem.getMessage)
            return
          case Right(naked) if naked.isEmpty =>
            println(s"$file is well typed.\n")
          case Right(naked) if ! naked.isEmpty =>
            naked.foreach {
              case (t, τ, tok) =>
                val name = tok.fileLine
                println(s"$name : ${τ.unparse}")
                println(s"$name = ${t.unparse}")
                println()
            }
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
