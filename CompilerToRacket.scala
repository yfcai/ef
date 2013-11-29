trait Racketeer extends Terms {
  trait RacketSyntax extends TermVisitor[Seq[String]] {
    private[this] type T = Seq[String]

    def χ(name: Name): T = Seq(name.toString)

    def λ(name: Name, body: T): T =
      s"(λ (${name.toString}) " +: body :+ ")"

    def ε(operator: T, operand: T): T =
      // Simple application doesn't work.
      //
      //   "(" +: (operator ++ (" " +: operand :+ ")"))
      //
      // Racket wants identifier at operator position.
      // I'm exasperated.
      "(let ([ex∀sperated " +:
      (operator ++ ("]) (ex∀sperated " +: operand :+ "))"))
  }

  object RacketSyntax extends RacketSyntax

  def toRacket(t: Term): String = RacketSyntax(t).mkString

  val racketPrelude =
    s"""
    |#lang lazy
    |(!! (let* (
    |[fix (λ (f) ((λ (x) (f (x x))) (λ (x)(f (x x)))))]
    |[+ (λ (x) (λ (y) (+ x y)))]
    |[nil null]
    |[cons (λ (x) (λ (xs) (cons x xs)))]
    |[churchTrue  (λ (x) (λ (y) x))]
    |[churchFalse (λ (x) (λ (y) y))]
    |[isnil (λ (l) (if (null? l) churchTrue churchFalse))]
    |[head (λ (l) (car l))]
    |[tail (λ (l) (cdr l))]
    |)
    |""".stripMargin

  val racketFinale = "))"
}

object CompilerToRacket extends FileParser with Racketeer {
  def process(result: List[Expr]): Unit = {
    println(racketPrelude)
    result foreach {
      case DefExpr(name, term) =>
        println(s"(define $name ${toRacket(term.getTerm)})")
        println()

      case NakedExpr(term) =>
        println(toRacket(term.getTerm))
        println()
    }
    println(racketFinale)
  }
}
