/*
trait Types extends Trees {
  case object Type extends Genus
  // æ
}

trait Terms extends Types {
  // terms, no boilerplate
  case object Term extends Genus
  // try make them operators
  /*
  case object FreeVar extends FreeName(Term)
  case object Var extends DeBruijn(Term)
  case object Abs extends Binder(Var, Term, Term)
  case object App extends Tag(Term, Term, Term)

  // extrapolate BinderFactory after more examples
  object λ {
    def apply(x: String)(body: Tree): Tree =
      ⊹(Abs, §(x), body.imprison(Var, x, 0))
  }
  object χ extends LeafFactory[String](FreeVar)
   */
}*/

trait Syntax extends Operators {
  // keywords (always a token by itself):
  val keywords = "( ) [ ] { } ∀ ∃ Λ λ .".words

  // things that can't be a name:
  val forbidden = "( ) .".words

  implicit class SplitStringIntoWords(s: String) {
    def words: Set[String] = Set(s split " ": _*)
  }

/*
  case object Atomic extends Operator(LoneToken(forbidden), Nil)

  // ... super constructor cannot be passed a self reference
  // unless parameter is declared by-name ... (facepalm)
  def functorApplicationSelfReference = FunctorApplication

  case object FunctorApplication extends Operator(
    Juxtaposition,
    Seq(downFrom(functorApplicationSelfReference, typeOps),
        downFrom(TypeParenthetic, typeOps))
  )

  case object TermApplication extends Operator(
    Juxtaposition,
    Seq(downFrom(TypeInstantiation, termOps),
        downFrom(TermParenthetic  , termOps))
  )

  case object TypeAmnesia extends Operator(
    Infixl(":"),
    Seq(downFrom(TypeInstantiation, termOps),
        typeOps)
  )

  def typeInstantiationSelfReference  = TypeInstantiation

  case object TypeInstantiation extends Operator(
    Postfix("[", "]"),
    Seq(downFrom(typeInstantiationSelfReference, termOps), typeOps)
  )

  def functionArrowSelfReference = FunctionArrow

  case object FunctionArrow extends Operator(
    Infixr("→"),
    // allowing all type expressions to appear on rhs of arrow
    Seq(downBelow(functionArrowSelfReference, typeOps), typeOps)
  )

  def typeParameterListSelfReference = TypeParameterList

  case object TypeParameterList extends Operator(
    IndividualTokens,
    _ map (_ => Seq(Atomic))
  )

  case object ExistentialQuantification extends Operator(
    Prefix("∃", "."),
    Seq(Seq(TypeParameterList), typeOps)
  )

  case object UniversalQuantification extends Operator(
    Prefix("∀", "."),
    Seq(Seq(TypeParameterList), typeOps)
  )

  case object TypeAbstraction extends Operator(
    Prefix("Λ", "."),
    Seq(Seq(TypeParameterList), termOps)
  )

  case object TermAbstraction extends Operator(
    Prefix("λ", ":", "."),
    Seq(Seq(Atomic), typeOps, termOps)
  )

  case object LetBinding extends Operator(
    Prefix("let", "=", "in"),
    Seq(Seq(Atomic), termOps, termOps)
  )
*/

  val typeOps: List[Operator] =
    List()
    /*
    List(
      UniversalQuantification   ,
      ExistentialQuantification ,
      FunctionArrow             ,
      FunctorApplication        ,
      Atomic                    )
     */

  val termOps: List[Operator] =
    List()
    /*
    List(
      LetBinding        ,
      TermAbstraction   ,
      TypeAbstraction   ,
      TypeAmnesia       ,
      TypeInstantiation ,
      TermApplication   ,
      Atomic            )
     */

  def downFrom(x: Operator, ops: List[Operator]): List[Operator] =
    ops match {
      case y :: tail if x == y => ops
      case _ :: tail => downFrom(x, tail)
      case Nil => sys error s"$x not found in $ops"
    }

  def downBelow(x: Operator, ops: List[Operator]): List[Operator] =
    downFrom(x, ops) match {
      case Nil | _ :: Nil => sys error s"nothing below $x in $ops"
      case x :: tail => tail
    }
}
