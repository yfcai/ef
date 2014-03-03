trait ConstrainedTypes extends Syntax { typing =>
    case object InstantiationConstraint extends BinaryOperator {
      val fixity: Fixity = Infixr(Seq("⊑", "<precedes>"))
      def lhs = downFrom(FunctionArrow, typeOps)
      def rhs = downFrom(FunctionArrow, typeOps)

      // while it may be hard to imagine the constraint as
      // a type, it had better be, so that strings are
      // understood as free type variables.
      def opGenus = BinaryOpGenus(Type, Type, Type)
    }

    case object ConstraintList extends Operator {
      val fixity: Fixity = Infixr(",") orElse CompositeItem

      def genus = Type

      def tryNext = ???
      override
      def tryNextOverride: Seq[Seq[Tree]] => Seq[Seq[Operator]] =
        _ map (_ => Seq(InstantiationConstraint))

      def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)
    }

    case object ConstrainedType extends Operator {
      def genus = Type

      val fixity: Fixity = Infixl("given")
      def tryNext = Seq(
        downFrom(FunctionArrow, typeOps),
        Seq(ConstraintList))

      def cons(children: Seq[Tree]): Tree = ⊹(this, children: _*)

      def apply(τ: Tree, constraints: Seq[Tree]): Tree = {
        assert(! constraints.isEmpty) // if empty, can't unparse
        cons(τ :: ConstraintList.cons(constraints) :: Nil)
      }

      def unapply(σ: Tree): Option[(Tree, Seq[Tree])] = σ match {
        case ⊹(ConstrainedType, τ, ⊹(ConstraintList, constraints @ _*)) =>
          Some((τ, constraints))
        case _ =>
          None
      }

      override def unparse(t: Tree): String = t match {
        case ConstrainedType(τ, constraints) =>
          val unparsedConstraints =
            constraints.map(_.unparse).mkString(", ")
          s"(${τ.unparse} given ${unparsedConstraints})"
      }
    }

    object ⊑ extends BinaryFactory(InstantiationConstraint)
    implicit class InstantiationConstrained(σ: Tree) {
      def ⊑ (τ: Tree) = typing.⊑(σ, τ)
    }
}