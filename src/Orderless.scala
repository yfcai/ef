/** constraint-based type checking
  * without regard for the order of quantifiers.
  * may be inconsistent, may be unsound;
  * goal is to get familiar with solving constraints.
  */
trait Orderless extends TypedModules with IntsAndBools {
  def typeCheck(m: Module):
      Either[Problem, Seq[(Tree, Tree, Token)]] =
    ???

  class OrderlessTyping(module: Module) extends SynonymResolution(module)
  {
    import module._

    // INSTANTIATION CONSTRAINTS

    case class ⊑ (lhs: Tree, rhs: Tree) {
      lazy val freeNames: Set[String] =
        lhs.freeNames ++ rhs.freeNames
    }

    implicit class InstantiationConstrained(σ: Tree) {
      def ⊑ (τ: Tree) = new ⊑(σ, τ)
    }

    case class Domain(
      prefix: List[(String, Binder)],
      constraints: List[⊑],
      representative: Tree
    ) {
      lazy val freeNames: Set[String] =
        representative.freeNames ++
          prefix.map(_._1) ++
          constraints.flatMap(_.freeNames)
    }

    object Domain {
      // injection
      def apply(τ: Tree): Domain =
        Domain(Nil, Nil, τ)

      def fromApplication(fun: Domain, arg: Domain): Domain = {
        val Seq(a, b) =
          ABCSong.newNames(Seq("a", "b"), fun.freeNames ++ arg.freeNames)
        Domain(
          (a, Universal) :: (b, Universal) ::
            fun.prefix ++ arg.prefix,
          fun.representative ⊑ →(æ(a), æ(b)) ::
            arg.representative ⊑ æ(a) ::
            fun.constraints ++ arg.constraints,
          æ(b))
      }
    }

    // DOMAIN RECONSTRUCTION

    // Currently, no effort is expanded toward converting
    // types to prenex form.
    //
    // TODO: pull all the covariant universals to the place
    // where we want them.
    //
    // Question: what about existentials?
    // Answer: If we have a problem, then commit everything,
    // make a tag. Because it will be an example showing that
    // existentials are necessary.
    def gatherConstraints(
      term    : Tree,
      Γ       : Map[String, Tree],
      Δ       : Set[String],
      globals : PartialFunction[String, Tree]):
        Domain = term match {
      case χ(x) =>
        if (Γ contains x)
          Domain(Γ(x))
        else if (globals isDefinedAt x)
          Domain(globals(x))
        else
          sys error s"please discover unsubs in a preliminary scan"

      case fun ₋ arg =>
        Domain.fromApplication(
          gatherConstraints(fun, Γ, Δ, globals),
          gatherConstraints(arg, Γ, Δ, globals))

      case λ(x, σ, body) =>
        val toQuantify = σ.freeNames -- Δ
        val new_Γ = Γ.updated(x, σ)
        val new_Δ = Δ ++ toQuantify
        val dom = gatherConstraints(body, new_Γ, new_Δ, globals)
        Domain(
          dom.prefix,
          dom.constraints,
          ∀(toQuantify.toSeq: _*)(→(σ, dom.representative)))
    }

    case class Contradiction(
      msg: String,
      prefix: List[(String, Binder)],
      constraints: List[⊑])
        extends Exception (
      s"""|TODO: write me!
          |""".stripMargin
    )

    def contradiction(dom: Domain): Option[Contradiction] =
      ??? // TODO: write me first!
  }
}
