trait MinimalQuantification extends Prenex {
    def flipTag(tag: Binder): Binder = tag match {
      case Universal   => Existential
      case Existential => Universal
    }

  def quantifyMinimally(τ: Tree, avoid: Set[String]): Tree = {
      val (prenex, newAvoid) = Prenex(τ, avoid)
      prenex.prefix.foldLeft(prenex.body) {
        case (body, BinderSpec(quantifier, x, Annotation.none())) =>
          quantifyMinimally(x, quantifier, body, newAvoid)
      }
    }

    def quantifyMinimally(
      x: String,
      quantifier: Binder,
      τ: Tree,
      avoid: Set[String]
    ): Tree =
      if (τ.freeNames contains x) {
        τ match {
          case σ0 → σ1 if ! σ1.freeNames.contains(x) =>
            →(quantifyMinimally(x, flipTag(quantifier), σ0, avoid), σ1)

          case σ0 → σ1 if ! σ0.freeNames.contains(x) =>
            →(σ0, quantifyMinimally(x, quantifier, σ1, avoid))

          case ⊹(binder: Binder,  _*) =>
            binder.unbind(τ, avoid).get match {
              case (y, Seq(Annotation.none(), body)) =>
                binder.bind(y.get, Annotation.none(),
                  quantifyMinimally(x, quantifier, body, avoid))
            }

          case τ =>
            quantifier.bind(x, Annotation.none(), τ)
        }
      }
      else
        τ
}
