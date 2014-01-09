/** the type system */
trait ExistentialF extends Unification with Prenex {
  // divide the prefix of a type in prenex form
  // (wastful traversals of prenexPrefix, optimization opportunity)
  case class Prefix(prenexPrefix: Seq[PrenexSpec]) {
    val universals               = extractSet(UniversalQuantification)
    val universalBounds          = extractSet(UniversalBound)
    val universalUncertainties   = extractSet(UniversalUncertainty)
    val existentials             = extractSet(ExistentialQuantification)
    val existentialBounds        = extractSet(ExistentialBound)
    val existentialUncertainties = extractSet(ExistentialUncertainty)

    // debt of uncertain families, to be discharged
    // when the family breaks up
    val debt =
      extractMap(TypeList, UniversalUncertainty, ExistentialUncertainty)

    // maps children to the name of their parent
    val parent =
      extractMap(FreeTypeVar, UniversalBound, ExistentialBound)

    // maps parent to the names of their children
    val children: Map[String, Set[String]] =
      prenexPrefix.foldLeft(Map.empty[String, Set[String]]) {
        case (acc, PrenexSpec(tag, parent, _))
            if Seq(UniversalUncertainty, ExistentialUncertainty).
                 contains(tag) =>
          // paranoid verification of consistency:
          // parent must come before children.
          assert(! acc.contains(parent))
          acc.updated(parent, Set())
        case (acc, PrenexSpec(tag, child, Prenex(Seq(), parentNode)))
            if Seq(UniversalBound, ExistentialBound) contains tag =>
          val parent = FreeTypeVar get parentNode
          acc.updated(parent, acc(parent) + child)
        case (acc, _) =>
          acc
      }

    private[this]
    def extractSet(tag: Tag): Set[String] =
      prenexPrefix.withFilter(_.tag == tag).map(_.x)(collection.breakOut)

    private[this]
    def extractMap[T](leafTag: KnownLeafTag[T], tags: Tag*):
        Map[String, T] = extractMap0(tags, leafTag get _)

    private[this]
    def extractMap0[T](tags: Seq[Tag], extraction: Tree => T):
        Map[String, T] =
      extractMap1[T](
        tags contains _.tag,
        _.annotations match {
          case Seq(Prenex(Seq(), note)) => extraction(note)
        }
      )

    private[this]
    def extractMap1[T](predicate : PrenexSpec => Boolean,
                       extraction: PrenexSpec => T):
        Map[String, T] =
      extractMap2(predicate, spec => (spec.x, extraction(spec)))

    private[this]
    def extractMap2[T](predicate : PrenexSpec => Boolean,
                       extraction: PrenexSpec => (String, T)):
        Map[String, T] =
      prenexPrefix.withFilter(predicate).
        map(extraction)(collection.breakOut)
  }
}
