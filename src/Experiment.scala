trait ExperimentSubjects extends Parser with EFTypes {
  val rant =
    """|. rant
       |
       |  All the whores and politicians will look
       |  up to me and shout, "save us!"
       |
       |  I will look down and whisper, "no".
       |""".stripMargin

  val loremIpsum =
    """|      	
       |
       |.lorem ipsum
       |. dolor sit amet
       |Lorem ipsum
       |                      	
       |dolor sit amet
       | lorem ipsum
       |.yoyo .8
       |  dolor sit amet
       |. okayish
       |lorem ipsum dolor sit amet
       |
       |  . wow
       |  . rant
       |     . this is a fake rant
       |""".stripMargin + rant


  val someModule = rant +
    """|type List α = ∀β. β → (α → β → β) → β
       |cons  : ℤ → List ℤ → List ℤ
       |cons2 : ℤ → List ℤ → List ℤ
       |five = (Λα. λx : ℤ. + ((λx : ℤ. x) 2) 2) [ℤ]
       |         ((λx : ℤ → ℤ. x 5) (λx : ℤ. x)) {∃α. α}
       |cons  x xs = λz : β. λ++ : (ℤ → β → β). ++ x (xs z ++)
       |cons2 y ys = λa : γ. λ-- : (ℤ → γ → γ). -- y (ys a --)
       |
       |shadowedTerm = λx x x x x. x
       |shadowedType = ∀α α α. ∃α α. ∀α. α → α
       |""".stripMargin


  val consType =
    """|∀α. α → (∀β. β → (α → β → β) → β) → (∀β. β → (α → β → β) → β)
       |""".stripMargin

  val margaris19: List[String] =
    List(
      "∀α α α. ∃α α. ∀α. α → α",
      "(∀α. P) → (∀α. P)",
      "(∀α. P α) → (∃α. Q α)",
      "(∀α. P α) → (∃α. P α → ⊥) → ⊥",
      "(∀α. P α → ⊥) → (∃α. P α) → ⊥",
      "(∃α. P α) → (∃α. Q α) → ∃α. P α → Q α"
    )

  object Hmf {
    val pair       = "∀α β. α → β → Pair α β"
    val uncurry    = "∀α β γ. (α → β → γ) → Pair α β → γ"
    val app        = "∀α β. (α → β) → α → β"
    val truth      = "Bool"
    val falsehood  = "Bool"
    val ifThenElse = "∀α. Bool → α → α → α"
    val cons       = "∀α. α → List α → List α"
    val nil        = "∀α. List α"
    val foldr      = "∀α β. α → (α → β → β) → List α → β"
    val undefined  = "∀α. α"
    val foldrUndef = "∀α β. (α → β → β) → List α → β"
    val const      = "∀α β. α → β → α"
    val flip       = "∀α β γ. (α → β → γ) → β → α → γ"
    val revapp     = "∀α β. α → (α → β) → β"
    val poly       = "(∀ε. ε → ε) → Pair ℤ String"
    val id         = "∀α. α → α"
    val revappId   = "∀α β. ((α → α) → β) → β"
  }

  val hmfApps: List[(String, String)] = {
    import Hmf._
    List(
      (foldr, undefined),
      (foldrUndef, const),
      (flip, app),
      (revapp, id),
      (revappId, poly)
    )
  }
}

object Experiment extends ExperimentSubjects {
  def thisFile: String =
    new Throwable().getStackTrace().head.getFileName

  def toPrenex(s: String): String = PrenexForm(toType(s)).toType.unparse

  def toType(s: String): Type = (TypeExpr parse s).get.toType

  // precondition: fType is function type.
  def provisionalMgs(fType: Type, xType: Type): Map[α, Type] = {
    val PrenexForm(all1, _, σ1 → τ) = PrenexForm(fType)
    val PrenexForm(all2, _, σ2    ) = PrenexForm(xType)
    resolveConstraints(all1 ++ all2, σ1 ≡ σ2)
  }

  def prettifyMgs(mgs: Map[α, Type]): String =
    mgs.toList.sortBy(_._1.binder.name).map({
      case (β, τ) => s"$β ::= ${τ.unparse}"
    }) mkString "\n"

  def testParagraphs(s: String, p: Paragraphs) {
    println("TESTING PARAGRAPHS")
    println("==================")
    println(s.lines.zipWithIndex.map({
      case (line, linenum) =>
        "%3d: %s" format (linenum + 1, line)
    }) mkString "\n")
    println
    println(p mkString "\n\n")
    println
  }

  def testParagraphs(s: String) {
    testParagraphs(s, Paragraphs(s))
  }

  def testParagraphsFromFile(path: String) {
    val s = (scala.io.Source fromFile path).getLines mkString "\n"
    testParagraphs(s, Paragraphs fromFile path)
  }

  def testModule() {
    val module = parse(someModule)
    println(module.unparse)
    println
    val five  = module definitions ξ("five")
    val cons  = module definitions ξ("cons")
    val cons2 = module definitions ξ("cons2")
    println(s"${cons α_equiv five  }: cons ≅ five")
    println(s"${cons α_equiv cons2} : cons ≅ cons2")
  }

  def testPrenex() {
    margaris19 foreach {
      theorem => println(s"$theorem  =  ${toPrenex(theorem)}")
    }
  }

  def testApp(fType: String, xType: String) {
    val (f, x) = (toType(fType), toType(xType))
    println(s"fun : ${f.unparse}")
    println(s"arg : ${x.unparse}")
    val τ = getResultTypeOfApplication(f, x)
    println(s"ret : ${τ.unparse}")
    println
  }

  def testUnification() {
    hmfApps foreach { case (f, x) => testApp(f, x) }
  }

  def main(args: Array[String]) {
    testUnification
  }
}
