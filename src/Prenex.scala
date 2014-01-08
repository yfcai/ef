/** Prenex forms for Existential F */
trait Prenex extends Syntax {
  case class Prenex(prefix: Seq[PrenexSpec], body: Tree) {
    def toType: Tree = body.boundBy(prefix.map(_.toBinderSpec))

    def flipPrefix: Seq[PrenexSpec] = prefix.map({
      case PrenexSpec(tag, x, annotations @ _*) =>
        val flippedTag = tag match {
          case UniversalQuantification =>
            ExistentialQuantification
          case ExistentialQuantification =>
            UniversalQuantification
          case UniversalBound =>
            ExistentialBound
          case ExistentialBound =>
            UniversalBound
          case UniversalUncertainty =>
            ExistentialUncertainty
          case ExistentialUncertainty =>
            UniversalUncertainty
        }
        PrenexSpec(flippedTag, x, annotations: _*)
    })
  }

  case class PrenexSpec(tag: Binder, x: String, annotations: Prenex*) {
    def toBinderSpec = BinderSpec(tag, x, annotations.map(_.toType): _*)
  }

  object Prenex {
    def apply(τ: Tree, toAvoid: Set[String]): (Prenex, Set[String]) = {
      val (rawPrefix, rawBody) = τ.unbindAll(toAvoid, _ => true)
      val undesirables1 = toAvoid ++ rawPrefix.map(_.x)
      val (prefix, undesirables2) = PrenexSpec(rawPrefix, undesirables1)
      val (pbody, undesirables3) = ofMonotype(rawBody, undesirables2)
      (Prenex(prefix ++ pbody.prefix, pbody.body), undesirables3)
    }

    def apply(types: Seq[Tree], toAvoid: Set[String]):
        (Seq[Prenex], Set[String]) =
      types.foldRight[(Seq[Prenex], Set[String])]((Nil, toAvoid)) {
        case (τ, (prenexes, toAvoid)) =>
          val (prenex, undesirables) = Prenex(τ, toAvoid)
          (prenex +: prenexes, undesirables)
      }

    def ofMonotype(monotype: Tree, toAvoid: Set[String]):
        (Prenex, Set[String]) = monotype match {
      case σ → τ =>
        val (Seq(ps, pt), undesirables) = Prenex(Seq(σ, τ), toAvoid)
        (Prenex(ps.flipPrefix ++ pt.prefix, →(ps.body, pt.body)),
          undesirables)

      case σ □ τ =>
        val (Seq(ps, pt), undesirables) = Prenex(Seq(σ, τ), toAvoid)
        (Prenex(ps.prefix ++ pt.prefix, □(ps.body, pt.body)), undesirables)

      case ⊹(tag, _) =>
        sys error s"object Prenex isn't aware of $tag"

      case leaf @ ∙(_, _) =>
        (Prenex(Nil, leaf), toAvoid)
    }
  }

  object PrenexSpec {
    def apply(spec: BinderSpec, toAvoid: Set[String]):
        (PrenexSpec, Set[String]) = spec match {
      case BinderSpec(tag, x, notes @ _*) =>
        val (prenexes, undesirables) = Prenex(notes, toAvoid)
        (PrenexSpec(tag, x, prenexes: _*), undesirables)
    }

    def apply(specs: Seq[BinderSpec], toAvoid: Set[String]):
        (Seq[PrenexSpec], Set[String]) =
      specs.foldRight[(Seq[PrenexSpec], Set[String])]((Nil, toAvoid)) {
        case (binderSpec, (specs, toAvoid)) =>
          val (spec, undesirables) = PrenexSpec(binderSpec, toAvoid)
          (spec +: specs, undesirables)
      }
  }
}
