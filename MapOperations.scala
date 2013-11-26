import scala.language.implicitConversions

trait MapOperations {
  implicit class ConvenientMapOpsForSMF[K, V](m: Map[K, V]) {
    def inverse: Map[V, K] = m map (_.swap)

    def restrict(subdomain: Iterable[K]): Map[K, V] =
      subdomain.flatMap({
        k => if (m contains k) Some(k -> m(k)) else None
      })(collection.breakOut)
  }
}
