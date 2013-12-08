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

trait RacketFileParser extends FileParser with Racketeer {
  def getRacketCode(result: List[Expr]): String = {
    (racketPrelude +:
      (result map {
        case DefExpr(name, term) =>
          s"(define $name ${toRacket(term.getTerm)})"
        case NakedExpr(term) =>
          toRacket(term.getTerm)
      }) :+ racketFinale).mkString
  }
}

object CompilerToRacket extends RacketFileParser {
  def process(result: List[Expr]) {
    println(getRacketCode(result))
  }
}

object ExecuterInRacket extends RacketFileParser {
  def process(result: List[Expr]) {
    // cargo code from:
    // http://stackoverflow.com/a/6041248
    import sys.process._
    val code = getRacketCode(result)
    val proc = Process("racket /dev/stdin")
    val io = new ProcessIO (
      in  => {in.write(code getBytes "UTF-8") ; in.close},
      out => {scala.io.Source.fromInputStream(out).getLines.foreach(println)},
      err => {scala.io.Source.fromInputStream(err).getLines.foreach(println)})
    proc run io
  }
}