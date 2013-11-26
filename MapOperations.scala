import scala.language.implicitConversions

trait MapOperations {
  implicit class ConvenientMapOpsForSMF[K, V](m: Map[K, V]) {
    def inverse: Map[V, K] = m map (_.swap)

    def restrict(subdomain: Set[K]): Map[K, V] =
      if (subdomain.size < m.size)
        subdomain.flatMap({
          k => if (m contains k) Some(k -> m(k)) else None
        })(collection.breakOut)
      else
        m filter (subdomain contains _._1)
  }
}
