trait Calculi {
  trait Calculus extends TypedModules with ReductionSemantics {
    def eval(t: Tree, module: Module): Tree = eval(module.dfn)(t)
  }

  object ExistentialFCalculus extends Calculus with ExistentialF

  trait Executable {
    def run(file: String, c: Calculus)(module: c.Module): Unit

    def err(s: Any) = System.err.println(s.toString)
    def print(s: Any) = { System.out.print(s) ; System.out.flush() }

    def debug: Boolean = false

    def execute(args: Array[String], debug: Boolean): Unit =
      try {
        args.foreach { file =>
          val calculus: Calculus = calculusOfFile(file)
          val module = try {
            calculus.Module.fromFile(file)
          } catch {
            case _: java.io.FileNotFoundException =>
              throw new java.io.FileNotFoundException(s"$file: not found")
          }
          run(file, calculus)(module)
        }
      } catch {
        case e: Exception =>
          if (debug)
            throw e
          else
            err(e.getMessage)
      }
  }

  class UnknownExtensionException(file: String)
      extends Exception(s"$file: unknown extension")

  def calculusOfFile(file: String): Calculus =
    file.substring(file.lastIndexOf(".") + 1) match {
      case "ef" => ExistentialFCalculus
      case _    => throw new UnknownExtensionException(file)
    }

  object Reductionist extends Executable {
    def run(file: String, c: Calculus)(module: c.Module) {
      module.naked.foreach {
        case (t, tok +: _) =>
          println(s"${tok.fileLine} = ${c.eval(t, module).unparse}")
          println()
      }
    }
  }

  object TypeChecker extends Executable {
    def run(file: String, c: Calculus)(module: c.Module) {
        c.typeCheck(module) match {
          case Left(problem) =>
            throw problem
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
    }
  }

  object Executioner extends Executable {
    def run(file: String, c: Calculus)(module: c.Module) {
        c.typeCheck(module) match {
          case Left(problem) =>
            throw problem
          case Right(naked) if naked.isEmpty =>
            println(s"$file is well typed.\n")
          case Right(naked) if ! naked.isEmpty =>
            naked.foreach {
              case (t, τ, tok) =>
                val name = tok.fileLine
                val xxxx = Array.fill(name.length)(' ').mkString
                println(s"$name : ${τ.unparse}")
                println(s"$name = ${t.unparse}")
                println(s"$xxxx = ${c.eval(t, module).unparse}")
                println()
            }
        }
    }
  }
}
