case class UniversalSet[A](negated: Set[A] = Set.empty[A]) extends Set[A]
{
  def iterator: Iterator[A] =
    sys error "Iterating over a universal set is impossible."

  def contains(key: A): Boolean = ! (negated contains key)

  def +(elem: A): UniversalSet[A] = UniversalSet(negated - elem)

  def -(elem: A): UniversalSet[A] = UniversalSet(negated + elem)
}
