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

// try 2: small-step
trait SmallStepSemantics extends Syntax {
  type Reduction = PartialFunction[Tree, Tree]

  /** @return (thing inside context, evalutation context) */
  def callByValue(t: Tree, reduction: Reduction):
      (Tree, Tree => Tree) = t match {
    case s ₋ t =>
      val (ins, cs) = callByValue(s, reduction)
      if (ins != s)
        (ins, x => ₋(cs(x), t))
      else {
        val (int, ct) = callByValue(t, reduction)
        (int, x => ₋(s, ct(x)))
      }

    case _ =>
      (t, identity)
  }

  // untyped β-reduction
  val beta: Reduction = {
    // not using λ here due to inherent unbinding involved
    case ₋(f, x) if f.tag == AnnotatedAbstraction => f(x)
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
      val i = n.toInt
      if (i == 0)
        z
      else if (i > 0)
        ₋(₋(₋(χ("iterate"), χ((i - 1).toString)), ₋(f, z)), f)
      else
        χ("???")

    // absurdity
    case χ("???") ₋ _ =>
      sys error s"applying absurdity"
  }
}

trait SmallStepRepl extends SmallStepSemantics with Modules with SystemF {
  import scala.tools.jline.console._
  import completer._
  import collection.JavaConversions._

  var typeSystem: SystemFTyping = new SystemFTyping(Module.empty)

  def module: Module = typeSystem.module

  def getType(ttoks: (Tree, Seq[Token])): String =
    typeSystem.getType(ttoks._1, ttoks._2) match {
      case Left(problem) => problem.getMessage
      case Right(typ) => s"${typ.unparse}\n"
    }

  val console = new ConsoleReader

  assert(console.addCompleter(
    new ArgumentCompleter(List(EnvCompleter, new FileNameCompleter))))

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
              put(getType(Term.parse(ProtoAST(t.unparse)).get))
          }
        }
      } catch {
        case p: Problem =>
          println(p.getMessage)
      }
    }
  }

  def load(file: String) {
    // todo: really load preludes
    io.Source.fromFile(file)
  }

  object Directive extends TopLevelGenus {
    lazy val ops = List(Help, Typing)
    // TODO: add Term & ParagraphExpr here
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

  def complainPolitely() =
    println(util.Random.nextInt(6) match {
      case 0 =>
        "I understand it's not your fault, but what did you just say?"
      case 1 =>
        "Can you help me with this? I don't comprehend."
      case 2 =>
        "I'm afrait we have a problem with communication."
      case 3 =>
        "UNRECOGNIZED DIRECTIVE"
      case 4 =>
        "I'm afraid there might be a misunderstanding."
      case 5 =>
        "Could you please paraphrase that, perhaps?"
    })


  object EnvCompleter extends Completer {
    type JavaList = java.util.List[CharSequence]
    def complete(prefix: String, cursor: Int, candidates: JavaList):
        Int = {
      val matches =
        module.dfn.keySet.filter(_ startsWith prefix).toSeq.sorted
      candidates addAll matches
      if (candidates.isEmpty)
        -1
      else
        0 // cargo code from StringCompleter
    }
  }
}
