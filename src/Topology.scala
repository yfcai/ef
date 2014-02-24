trait Topology {
  def getTopologicalOrder[T](graph: Map[T, Set[T]]):
      Map[T, Int] = topologicalOrder(graph) match {
    case Right(stuff) => stuff
    case Left(men) => sys error s"there's a cycle amongst $men"
  }

  def topologicalOrder[T](graph: Map[T, Set[T]]):
      Either[Set[T], Map[T, Int]] = {
    var distance = -1
    var toVisit  = graph.keySet
    var result   = Map.empty[T, Int]
    while (! toVisit.isEmpty) {
      val frontier = toVisit.filter {
        α => graph(α).find(toVisit contains _) == None
      }
      if (frontier.isEmpty)
        // cycle detected
        return Left(toVisit)
      distance = distance +  1
      toVisit  = toVisit  -- frontier
      result   = result   ++ frontier.map(α => (α, distance))
    }
    Right(result)
  }

  // duplicate code for collection.mutable.*
  def topologicalOrder[T](graph:
      collection.mutable.Map[T, collection.mutable.Set[T]]):
      Either[Set[T], Map[T, Int]] = {
    var distance = -1
    var toVisit  = graph.keySet
    var result   = Map.empty[T, Int]
    while (! toVisit.isEmpty) {
      val frontier = toVisit.filter {
        α => graph(α).find(toVisit contains _) == None
      }
      if (frontier.isEmpty)
        // cycle detected
        return Left(Set(toVisit.toSeq: _*))
      distance = distance +  1
      toVisit  = toVisit  -- frontier
      result   = result   ++ frontier.map(α => (α, distance))
    }
    Right(result)
  }
}
