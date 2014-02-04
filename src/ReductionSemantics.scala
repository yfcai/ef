// try 1: big step
trait ReductionSemantics extends Syntax {
  type Reduction = PartialFunction[Tree, Tree]

  // values
  object Val {
    def unapply(t: Tree): Option[Tree] = t.tag match {
      case AnnotatedAbstraction | FreeVar =>
        Some(t)
      case _ =>
        None
    }
  }

  /** @return (thing inside context, evalutation context)
    *
    * (This is unclear. Investigate how best to implement
    * evaluation contexts.)
    */
  def callByValue(t: Tree)(isRedex: Tree => Boolean):
      (Tree, Tree => Tree) = t match {
    case e if isRedex(e) =>
      (e, x => x)
    case e0 ₋ e1 if isRedex(e0) =>
      (e0, x => ₋(x, e1))
    case Val(v) ₋ e =>
      val (e2, c) = callByValue(e)(isRedex)
      (e2, x => ₋(v, c(x)))
    case e0 ₋ e1 =>
      val (e2, c) = callByValue(e0)(isRedex)
      if (isRedex(e2))
        (e2, x => ₋(c(x), e1))
      else {
        val (e3, c) = callByValue(e1)(isRedex)
        (e3, x => ₋(e0, c(x)))
      }
    case e =>
      (e, x => x)
  }

  // untyped β-reduction
  val beta: Reduction = {
    // not using λ here due to inherent unbinding involved
    case ₋(f, x) if f.tag == AnnotatedAbstraction => f(x)
  }

  // ignore top-level type annotations
  val erasure: Reduction = {
    case t if t.tag == TypeAbstraction =>
      TypeAbstraction.bodyOf(t)
    // ascription
    case Ascr(t, τ) =>
      t
    // instantiation
    case □(t, σ) =>
      t
  }

  val delta: Reduction = {
    // arithmetics
    case (χ("+") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt + rhs.toInt).toString)
    case (χ("-") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt - rhs.toInt).toString)
    case (χ("*") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt * rhs.toInt).toString)
    case (χ("/") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt / rhs.toInt).toString)
    case (χ("%") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt % rhs.toInt).toString)
    // integer comparisons
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≡" || op == "==" =>
      χ((lhs.toInt == rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "<" =>
      χ((lhs.toInt < rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == ">" =>
      χ((lhs.toInt > rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≤" || op == "<=" =>
      χ((lhs.toInt <= rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≥" || op == ">=" =>
      χ((lhs.toInt >= rhs.toInt).toString)
    // Church-encoded Booleans
    case (χ("true")  ₋ thenBranch) ₋ elseBranch =>
      thenBranch
    case (χ("false") ₋ thenBranch) ₋ elseBranch =>
      elseBranch
    // loops, coz recursion's too hard
    case ((χ("iterate") ₋ χ(n)) ₋ z) ₋ f =>
      Range(n.toInt, 0, -1).foldRight(z) {
        case (i, body) => ₋(₋(f, χ(i.toString)), body)
      }
    // absurdity
    case χ("???") ₋ _ =>
      sys error s"applying absurdity"
  }

  val reduction: Reduction = beta orElse delta orElse erasure

  def reduce(t: Tree, env: PartialFunction[String, Tree]):
      Option[Tree] = {
    val realReduction: Reduction = reduction orElse {
      case χ(name) if env.isDefinedAt(name) =>
        env(name)
    }
    val (redex, context) = callByValue(t)(realReduction.isDefinedAt)
    realReduction.andThen(Some.apply[Tree]).
      applyOrElse(redex, (_: Tree) => None).map(context)
  }

  def eval(env: PartialFunction[String, Tree])(t: Tree): Tree =
    reduce(t, env).fold(t)(eval(env))
}

// try 2: small-step for System F with primitive lists
trait SmallStepSemantics extends SystemF with PrimitiveLists {
  type Reduction = PartialFunction[Tree, Tree]

  /** @return (thing inside context, evalutation context) */
  def callByName(t: Tree, reduction: Reduction):
      (Tree, Tree => Tree) =
    getRedex(t, reduction).getOrElse((t, identity))

  def getRedex(t: Tree, reduction: Reduction):
      Option[(Tree, Tree => Tree)] =
    t match {
      // reduce first, ask questions later
      case _ if reduction isDefinedAt t =>
        Some((t, identity))

      case s ₋ t =>
        getRedex(s, reduction) match {
          case Some((redex, context)) =>
            Some((redex, x => ₋(context(x), t)))
          case None => getRedex(t, reduction).map {
            case (redex, context) => (redex, x => ₋(s, context(x)))
          }
        }

      case t □ τ =>
        getRedex(t, reduction).map {
          case (redex, context) => (redex, x => □(context(x), τ))
        }

      case _ =>
        None
    }

  def step(t: Tree, reduction: Reduction): Option[Tree] = {
    val (redex, context) = callByName(t, reduction)
    if (reduction isDefinedAt redex)
      Some(context(reduction(redex)))
    else
      None
  }

  def eval(t: Tree, reduction: Reduction): Tree = {
    // this elegant thing causes stack overflow when sorting
    // a list of 4 elements.
    //   step(t, reduction).fold(t)(s => eval(s, reduction))
    var current: Tree = null
    var next: Option[Tree] = Some(t)
    do {
      current = next.get
      next = step(current, reduction)
    }
    while (next != None)
    current
  }

  case class Stuck(s: String = "stuck") extends Exception(s)

  // untyped β-reduction
  val beta: Reduction = {
    // not using λ here due to inherent unbinding involved
    case f ₋ x if f.tag == AnnotatedAbstraction => f(x)
  }

  val instantiation: Reduction = {
    case t □ τ if t.tag == TypeAbstraction => t(τ)
  }

  val delta: Reduction = {
    // arithmetics
    case (χ("+") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt + rhs.toInt).toString)
    case (χ("-") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt - rhs.toInt).toString)
    case (χ("*") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt * rhs.toInt).toString)
    case (χ("/") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt / rhs.toInt).toString)
    case (χ("%") ₋ χ(lhs)) ₋ χ(rhs) =>
      χ((lhs.toInt % rhs.toInt).toString)
    // integer comparisons
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≡" || op == "==" =>
      χ((lhs.toInt == rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "<" =>
      χ((lhs.toInt < rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == ">" =>
      χ((lhs.toInt > rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≤" || op == "<=" =>
      χ((lhs.toInt <= rhs.toInt).toString)
    case (χ(op) ₋ χ(lhs)) ₋ χ(rhs)
        if op == "≥" || op == ">=" =>
      χ((lhs.toInt >= rhs.toInt).toString)
    // Church-encoded Booleans
    case ((χ("true" ) □ _)  ₋ thenBranch) ₋ elseBranch =>
      thenBranch
    case ((χ("false") □ _) ₋ thenBranch) ₋ elseBranch =>
      elseBranch
    // loops, coz recursion's too hard
    case (((χ("iterate") □ τ) ₋ χ(n)) ₋ z) ₋ f =>
      val i = n.toInt
      if (i == 0)
        z
      else if (i > 0)
        ₋(₋(₋(□(χ("iterate"), τ), χ((i - 1).toString)),
          ₋(₋(f, χ(n)), z)), f)
      else
        χ("???")
    // absurdity
    case χ("???") ₋ _ =>
      throw Stuck("applying absurdity")
    case χ("???") □ _ =>
      throw Stuck("instantiating absurdity")

    // lists
    case (χ("isnil") □ _) ₋ (χ("nil") □ _) =>
      χ("true")

    case (χ("isnil") □ _) ₋ (((χ("cons") □ _) ₋ _) ₋ _) =>
      χ("false")

    case (χ("head") □ _) ₋ (χ("nil") □ _) =>
      throw Stuck("head of empty list")

    case (χ("head") □ _) ₋ (((χ("cons") □ _) ₋ head) ₋ _) =>
      head

    case (χ("tail") □ _) ₋ (χ("nil") □ _) =>
      throw Stuck("tail of empty list")

    case (χ("tail") □ _) ₋ (((χ("cons") □ _) ₋ _) ₋ tail) =>
      tail
  }
}

trait SmallStepRepl extends SmallStepSemantics with Modules {
  import scala.tools.jline.console._
  import completer._

  // we want recursion here.
  recurseFlag = true

  var typeSystem: SystemFTyping = new SystemFTyping(Module.empty)

  def module: Module = typeSystem.module

  def getType(t0: Tree): Either[Problem, Tree] = {
    val (t, toks) = Term.parse(ProtoAST(t0.unparse)).get
    typeSystem.getType(t, toks)
  }

  def typeAndThen(t: Tree)(later: Tree => Unit): Unit =
    getType(t) match {
      case Left(problem) => println(problem.getMessage)
      case Right(τ) => later(τ)
    }

  val console = new ConsoleReader

  assert(console.addCompleter(
    ArgCompleter(EnvCompleter, JavaCompleter(new FileNameCompleter))))

  def startRepl() {
    def put(s: String) = { print(s) ; System.out.flush() }
    println(asciiArt)
    put(welcomeMessage)
    while (true) try {
      val line = console.readLine("> ")
      if (line == null) return ()
      else if (line.find(! _.isSpace) == None)
        ()
      else try {
        val directive = Directive.parse(line)
        if (directive == None)
          complainPolitely()
        else {
          directive.get match {
            case Quitter(_) =>
              return ()

            case Grammar(_) =>
              println(Grammar.message)

            case TypingRules(_) =>
              put(TypingRules.message)

            case Help(_) =>
              Help.show

            case About(_) =>
              put(About.message)

            case Ls(_) =>
              listTypes(module.sig)

            case Primitives(_) =>
              listTypes(arithmeticOperators ++ Γ0.finite)

            case Typing(t) =>
              typeAndThen(t)(τ => println(τ.unparse))

            case Step(t) =>
              typeAndThen(t)(τ => {
                printCurrentType(τ)
                printCurrentTerm(t)
                step(t)
              })

            case Load(§(file)) =>
              if (file.find(! _.isSpace) != None)
                load(file)
              else
                println("can only :load <one-file>")

            case Reload(_) =>
              module.maybeFile match {
                case Some(file) =>
                  load(file)
                case None =>
                  println("no file loaded yet; do you mean :l or :load ?")
              }

            // got definition, type & add it
            case definition @ Definition(x, t) =>
              if (t.freeNames contains x)
                println("Recursive definition is impossible in the REPL.")
              else if (Γ0.finite contains x)
                println(s"It is forbidden to override the primitive `$x`.")
              else typeAndThen(t) { τ =>
                // rename shadowed "x"
                val oldModule =
                  if (module.dfn contains x) {
                    val xOld = Postscript.newName(x, module.dfn.keySet)
                    val dfn = module.dfn map {
                      case (y, ydef) =>
                        (if (x == y) xOld else y, ydef.subst(χ(x), χ(xOld)))
                    }
                    val sig = module.sig map {
                      case (y, ytype) =>
                        (if (x == y) xOld else y, ytype)
                    }
                    val dfntoks = module.dfntoks.
                      updated(xOld, module.dfntoks(x))
                    val sigtoks = module.sigtoks.
                      updated(xOld, module.sigtoks(x))
                    Module(
                      module.syn, module.syntoks,
                      sig, sigtoks,
                      dfn, dfntoks,
                      module.naked).updateState(module)
                  }
                  else
                    module
                val toks = ParagraphExpr.parse(ProtoAST(line)).get._2
                val newModule = oldModule.add(definition, toks)
                new SystemFTyping(newModule).instrumentality match {
                  case Left(problem) => sys error s"fatal error: FFFFCAFE"
                  case Right(newTypeSystem) =>
                    typeSystem = newTypeSystem
                    println(s"$x : ${τ.unparse}")
                    println(s"$x = ${t.unparse}")
                }
              }

            // Got signature, warn.
            case Signature(_, _) =>
              println("type signature isn't supported in REPL")

            // Got type synonym, add it if okay
            case syn @ TypeSynonym(alpha, tau) =>
              if (typeSystem.Γ.types contains alpha)
                println(s"""$alpha is already bound to ${
                  typeSystem.resolve(æ(alpha)).unparse}""")
              else {
                val baddies = typeSystem.Γ.badTypes(tau.freeNames)
                if (! baddies.isEmpty)
                  throw typeSystem.
                    locateBadType(
                      typeSystem.Γ,
                      tau,
                      Type.parse(ProtoAST(tau.unparse)).get._2)
                else {
                  val toks = TypeSynonym.parse(ProtoAST(syn.unparse)).get._2
                  val newModule = module.add(syn, toks)
                  unsafeLoadModule(newModule)
                }
              }

            // got naked expression, type & evaluate it
            case NakedExpression(t) =>
              typeAndThen(t) { τ =>
                println(s" input : ${τ.unparse}")
                val v = eval(t, reduction)
                println(s"result = ${v.unparse}")
              }

            case otherwise =>
              println(s"unsurported in REPL: ${otherwise.tag}")
          }
        }
      } catch {
        case e: Exception => e match {
          case _: Problem
             | _: Stuck
             | _: java.io.FileNotFoundException =>
            val msg0 = e.getMessage
            val msg1 = if (msg0 endsWith "\n") msg0 else s"$msg0\n"
            put(msg1)
          case _ =>
            throw e
        }
      }
    }
    catch {
      case e: java.lang.StackOverflowError =>
        println("stack overflow")
    }
  }

  def unsafeLoadModule(m1: Module) {
    new SystemFTyping(m1).instrumentality match {
      case Right(ok) => typeSystem = ok
      case _ => sys error "fatal error: unsafeLoadModule"
    }
  }

  def load(file: String, silent: Boolean = false) {
    val newModule = Module.fromFile(file)
    val newTyping = new SystemFTyping(newModule)
    if (! silent) println(s"loading $file")
    newTyping.instrumentality match {
      case Left(problem) => throw problem
      case Right(perfection) => perfection.typeCheck match {
        case Left(problem) => throw problem
        case Right(stuff) =>
          typeSystem = perfection // hereby is old module discarded
          val naked = stuff.filter(_._1 == None)
          naked.foreach {
            case (defaultName, t, τ, tok) =>
              defaultName.fold({
                println()
                val name = if (silent) tok.fileLine else s":${tok.line}"
                val xxxx = Array.fill(name.length)(' ').mkString
                println(s"$name : ${τ.unparse}")
                println(s"$name = ${t.unparse}")
                println(s"$xxxx = ${eval(t, reduction).unparse}")
                })(_ => ())
              }
          }
    }
  }

  val arithmeticOperators: Map[String, Tree] = {
    val a   = if (I_hate_unicode) "a"   else "α"
    val int = if (I_hate_unicode) "Int" else "ℤ"
    val src = Map[String, String](
      "+ - * /" -> s"$int → $int → $int",
      "< == >" -> s"$int → $int → Bool",
      "<=  =>" -> s"$int → $int → Bool",
      "true" -> s"Bool",
      "false" -> s"Bool",
      "iterate" -> s"∀$a. $int → $a → ($int → $a → $a) → $a"
    )
    src.map(p => (p._1, Type(p._2)))
  }

  def listTypes(gamma: Map[String, Tree]): Unit =
    if (! gamma.isEmpty) {
      val ls = (gamma.map(identity)(collection.breakOut):
          List[(String, Tree)]).sortBy(_._1)
      val len = ls.map(_._1.length).max
      ls.foreach {
        case (x, τ) =>
          val pad = Array.fill(len - x.length)(' ').mkString
          println(s"$pad$x : ${τ.unparse}")
      }
    }

  def reduction: Reduction = ({
    case χ(x) if module.dfn contains x => module.dfn(x)
  }: Reduction) orElse beta orElse instantiation orElse delta

  def printCurrentType(τ: Tree) = println(s"current : ${τ.unparse}")
  def printCurrentTerm(t: Tree) = println(s"current = ${t.unparse}")

  def doneStepping(): Unit = println("done.")

  def screenWidth = 80

  def step(t0: Tree): Unit = getRedex(t0, reduction) match {
    case None => doneStepping()
    case Some((prev, context)) =>
      val next = reduction(prev)
      val innard = §({
        val line = s"    ${prev.unparse}  ==>  ${next.unparse}"
        if (line.length <= screenWidth)
          s"""|
              |  [
              |$line
              |  ]
              | """.stripMargin
        else
          s"""|
              |  [
              |    ${prev.unparse}  ==>
              |      ${next.unparse}
              |  ]
              | """.stripMargin
      })
      val spectacle = context(innard).unparse
      val t = context(next)
      println()
      println(spectacle)
      println()
      getType(t) match {
        case Left(problem) => throw Stuck("preservation failed")
        case Right(τ) =>
          printCurrentType(τ)
          printCurrentTerm(t)
          println()
          if (getRedex(t, reduction) != None) {
            var s = console.readLine("next? ")
            if (s == null)
              println()
            else s.find(! _.isSpace) match {
              case Some('n') | Some('N') =>
                ()
              case _ =>
                step(t)
            }
          }
          else
            doneStepping()
      }
  }

  object Directive extends TopLevelGenus {
    def commands = List(
      About,
      Grammar,
      Help,
      Load,
      Ls,
      Primitives,
      Quitter,
      Reload,
      Step,
      Typing,
      TypingRules)
    lazy val ops = commands :+ ParagraphExpr
  }

  def asciiArt =
    """|     _______
       |    / _____/
       |   / /__
       |  / ___/
       | / /
       |/_/
       |
       |System F
       |with recursion and call-by-name small-step reduction semantics
       |""".stripMargin

  def welcomeMessage =
    """|Input terms to normalize them.
       |Type :help for information dump.
       |""".stripMargin

  object About extends ObliviousCommand(":about") {
    def bio = "about this thing"

    def message =
      s"""|$asciiArt
          |by Yufei Cai
          |
          |for students of the lecture
          |"Programming languages and types"
          |in winter semester 2013/14
          |at the University of Marburg
          |
          |jar file assembled on 02.02.2014
          |""".stripMargin
  }

  trait UnicodeRehabilitation {
    def noUnicode = I_hate_unicode
    val a = if (noUnicode) "a"       else "α"
    val r = if (noUnicode) "->"      else "→"
    val u = if (noUnicode) "\\all "  else "∀"
    val l = if (noUnicode) "\\abs "  else "λ"
    val T = if (noUnicode) "\\Tabs " else "Λ"
  }

  object TypingRules
      extends ObliviousCommand(":tr", ":typing")
      with UnicodeRehabilitation {
    def bio = "display typing rules"

    def message: String = {
      val max = rules.flatMap(_._2.lines).map(_.length).max
      rules.flatMap({
        case (tag, rule) =>
          val lines = rule.lines.toSeq
          val len = lines.map(_.length).max
          val pad = max - len
          val padL = Array.fill(pad / 2          )(' ').mkString
          val padR = Array.fill(pad - padL.length)(' ').mkString
          List(
            padL + lines(0),
            padL + lines(1) + padR + s" ($tag)",
            padL + lines(2),
            "\n")
      }).mkString("\n")
    }

    val rules: List[(String, String)] = List(
      "T-Var"  -> """|gamma contains (x : T)
                     |----------------------
                     |   gamma |- x : T
                     |""".stripMargin,
      "T-Abs"  -> """|     gamma, x : T1  |- t2 : T2
                     |-------------------------------------
                     |gamma |- (\abs x : T1. t2) : T1 -> T2
                     |""".stripMargin,
      "T-App"  -> """|gamma |- t1 : T11 -> T12     gamma |- t2 : T11
                     |----------------------------------------------
                     |             gamma |- t1 t2 : T12
                     |""".stripMargin,
      "T-Tabs" -> """|         gamma |- t2 : T2
                     |-----------------------------------
                     |gamma |- (\Tabs a. t2) : \all a. T2
                     |""".stripMargin,
      "T-Tapp" -> """|          gamma |- t1 : \all a. T12
                     |---------------------------------------------
                     |gamma |- t1 [T2] : substitute T2 for a in T12
                     |""".stripMargin)
  }

  object Grammar
      extends ObliviousCommand(":g", ":grammar")
      with UnicodeRehabilitation {
    def bio = "display grammar"

    override def noUnicode = true // don't display unicode in grammar

    def message: String = {
      val max = grammar.map(_.length).max
      (grammar, explanation).zipped.map({
        case (line, comment) =>
          val pad = Array.fill(max - line.length + sep)(' ').mkString
          s"$line$pad$comment"
      }).mkString("\n")
    }

    def sep = 4

    def grammar =
      s"""|type ::= $a
          |       | type $r type
          |       | ${u}$a. type
          |
          |term ::= x
          |       | ${l}x. term
          |       | term term
          |       | ${T}$a. term
          |       | term [type]
          |""".stripMargin.lines.toSeq

    def explanation =
      s"""|type variable
          |type of functions
          |universal type
          |
          |variable
          |abstraction
          |application
          |type abstraction
          |type application
          |""".stripMargin.lines.toSeq
  }

  object Quitter extends ObliviousCommand(":q", ":quit") {
    def bio = "terminate this process"
  }

  object Help extends ObliviousCommand(":h", ":help") {
    def bio = "show help"

    def show() {
      println(
        "\nInput terms to normalize them; " +
        "use :s to step through reductions.\n")
      println("Files can be ran in batch by supplying them as\n" +
        "command-line arguments.\n")
      val items = Directive.commands.map(cmd =>
        (cmd.cmds.mkString(" "), cmd.bio))
      val len = items.map(_._1.length).max
      items.foreach {
        case (name, bio) =>
          val pad = Array.fill(len - name.length)(' ').mkString
          println(s"\n$pad$name   $bio")
      }
    }
  }

  object Step extends Command(":s", ":step") {
    def bio = "given a term, step through its reduction sequence"

    def tryNext = Seq(Term.ops)
  }

  object Ls extends ObliviousCommand(":ls", ":list") {
    def bio = "list the type of all visible definitions"
  }

  object Primitives extends ObliviousCommand(":p", ":primitives") {
    def bio = "list primitives"
  }

  object Load extends ObliviousCommand(":l", ":load") {
    def bio = "load definitions from a file"

    override
    def cons(children: Seq[Tree]): Tree =
      if (children.isEmpty)
        throw Stuck("usage:   :l <file-to-load>")
      else {
        val token = getFirstToken(children)
        val line  = token.paragraph.body
        val colon = line.indexWhere(! _.isSpace)
        val space = line.indexWhere(  _.isSpace, colon)
        val path  = line.indexWhere(! _.isSpace, space)
        val last  = line.lastIndexWhere(_.isSpace)
        val file  =
          if (colon < 0 | space < 0 | path < 0 | last < 0)
            ""
          else
            line.substring(path,
              if (last > path) last else line.length)
        ⊹(this, §(file))
      }
  }

  object Reload extends ObliviousCommand(":r", ":reload") {
    def bio = "reload previous file"
  }

  object Typing extends Command(":t", ":type") {
    def bio = "given a term, produce its type"

    def tryNext = Seq(Term.ops)
  }

  abstract class Command(val cmds: String*) extends Operator {
    def bio: String

    val fixity: Fixity = Prefixr(cmds)
    def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)
    def genus = Directive

    def unapply(t: Tree): Option[Tree] = t match {
      case ⊹(tag, child) if tag == this => Some(child)
      case _ => None
    }
  }

  abstract class ObliviousCommand(cmds: String*)
      extends Command(cmds: _*) {
    override val fixity = cmds.foldRight[Fixity](LoneToken(_ => false))({
      case (cmd, fix) => LoneToken(_ == cmd) orElse fix
    }) andThen1 AllItemsTogether
    def tryNext = Nil
  }

  val pleasantries = Array(
    "...DIRECTIVE?",
    "UNRECOGNIZED DIRECTIVE",
    "Need any :help to get started?",
    "I understand it's not your fault, but what's that supposed to mean?",
    "Can you help me with this? I don't comprehend.",
    "I'm afrait we have a problem with communication.",
    "I'm afraid there might be a misunderstanding.",
    "Could you paraphrase that, please?",
    "I'm sorry to say this, but maybe :help would help?",
    "In a perfect world, I'd see you proof-read the previous line.",
    "Excuse me, but there's a slight problem with the syntax of your command.")

  def complainPolitely() =
    println(pleasantries(util.Random.nextInt(pleasantries.length)))

  trait FunCompleter extends Completer {
    def complete(prefix: String): Seq[String]
  }

  // java interop trait
  trait ScalaCompleter extends FunCompleter {
    def complete(prefix: String): Seq[String]

    import collection.JavaConversions._
    private type JavaList = java.util.List[CharSequence]

    def complete(prefix: String, cursor: Int, candidates: JavaList):
        Int = {
      val matches = complete(prefix.substring(0, cursor))
      candidates addAll matches
      if (candidates.isEmpty) -1 else 0
    }
  }

  case class JavaCompleter(binks: Completer) extends FunCompleter {
    import collection.JavaConversions._
    private type JavaList = java.util.List[CharSequence]

    def complete(prefix: String): Seq[String] = {
      val list = new java.util.LinkedList[CharSequence]
      val i = complete(prefix, prefix.length, list)
      if (i > 0)
        list.map(prefix.substring(0, i) + _.toString)
      else
        list.map(_.toString)
    }

    def complete(prefix: String, cursor: Int, candidates: JavaList):
        Int = binks.complete(prefix, cursor, candidates)
  }

  case class ArgCompleter(children: FunCompleter*) extends ScalaCompleter {
    def complete(prefix: String): Seq[String] = {
      val args = prefix.split(" ").filter(! _.isEmpty)
      val precedence = args.init.mkString(" ")
      val filler = if (args.length <= 1) "" else " "
      if (args.isEmpty)
        Nil
      else for {
        child <- children
        result <- child.complete(args.last)
      } yield s"$precedence$filler$result"
    }
  }

  object EnvCompleter extends ScalaCompleter {
    def complete(prefix: String): Seq[String] =
      (Γ0.finite.keySet ++ module.dfn.keySet).
        toSeq.filter(_ startsWith prefix).sorted.map(_ + " ")
  }
}

object SmallStepRepl extends SmallStepRepl {
  def startRepl(files: Array[String]): Unit =
    if (files.isEmpty)
      startRepl()
    else try {
      files.foreach(file => load(file, silent = true))
    } catch {
      case e: Exception =>
        System.err.println(e.getMessage)
    }
}
