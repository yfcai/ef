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

  def eval(t: Tree, reduction: Reduction): Tree =
    step(t, reduction).fold(t)(s => eval(s, reduction))

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

    case (χ("head") □ _) ₋ (((χ("cons") □ _) ₋ _) ₋ tail) =>
      tail
  }
}

trait SmallStepRepl extends SmallStepSemantics with Modules {
  import scala.tools.jline.console._
  import completer._

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
    // TODO: ascii art
    def put(s: String) = { print(s) ; System.out.flush() }
    while (true) {
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
            case Help(_) =>
              put(Help.message)

            case Typing(t) =>
              typeAndThen(t)(τ => println(τ.unparse))

            // got naked expression, type & evaluate it
            case NakedExpression(t) =>
              typeAndThen(t) { τ =>
                println(s" input : ${τ.unparse}")
                val v = eval(t, reduction)
                println(s"result = ${v.unparse}")
              }
          }
        }
      } catch {
        case e: Problem => println(e.getMessage)
        case e: Stuck   => println(e.getMessage)
      }
    }
  }

  def load(file: String) {
    // todo: really load preludes
    io.Source.fromFile(file)
  }

  def reduction: Reduction = ({
    case χ(x) if module.dfn contains x => module.dfn(x)
  }: Reduction) orElse beta orElse instantiation orElse delta

  object Directive extends TopLevelGenus {
    lazy val ops = List(Help, Typing, ParagraphExpr)
  }

  object Help extends ObliviousCommand(":h", ":help") {
    def message = // TODO: replace this uplifting message.
      """|God helps those who helps themselves.
         |""".stripMargin
  }

  object Typing extends Command(":t", ":type") {
    def tryNext = Seq(Term.ops)
  }

  abstract class Command(cmds: String*) extends Operator {
    val fixity: Fixity = Prefixr(cmds)
    def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)
    def genus = Directive

    def unapply(t: Tree): Option[Tree] = t match {
      case ⊹(tag, child) if tag == this => Some(child)
      case _ => None
    }
  }

  class ObliviousCommand(cmds: String*)
      extends Command(cmds: _*) {
    override val fixity = cmds.foldRight[Fixity](LoneToken(_ => false))({
      case (cmd, fix) => LoneToken(_ == cmd) orElse fix
    }) andThen1 AllItemsTogether
    def tryNext = Nil
  }

  val pleasantries = Array(
    "...DIRECTIVE?",
    "UNRECOGNIZED DIRECTIVE",
    "I understand it's not your fault, but what did you just say?",
    "Can you help me with this? I don't comprehend.",
    "I'm afrait we have a problem with communication.",
    "I'm afraid there might be a misunderstanding.",
    "Could you please paraphrase that, perhaps?",
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
      complete(prefix, prefix.length, list)
      list.map(_.toString)
    }

    def complete(prefix: String, cursor: Int, candidates: JavaList):
        Int = binks.complete(prefix, cursor, candidates)
  }

  case class ArgCompleter(children: FunCompleter*) extends ScalaCompleter {
    def complete(prefix: String): Seq[String] = {
      val args = prefix.split(" ").filter(! _.isEmpty)
      if (args.isEmpty)
        Nil
      else for {
        child <- children
        result <- child.complete(args.last)
      } yield s"${args.init.mkString(" ")} $result "
    }
  }

  object EnvCompleter extends ScalaCompleter {
    def complete(prefix: String): Seq[String] =
      (Γ0.finite.keySet ++ module.dfn.keySet).
        toSeq.filter(_ startsWith prefix).sorted
  }
}
