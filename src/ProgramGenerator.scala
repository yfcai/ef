trait ProgramGenerator extends Syntax {
  trait SystemFGenerator {
    // we don't reset global name generator, ever.
    // worst case scenario: 9-character name (xFFFFFFFF).
    def withDepthLimit(depth: Int): Iterator[Tree] =
      termIterator(depth, initialNames, initialTypes)

    val globalNameGenerator = new GlobalNameGenerator

    def initialTypes = List("ℤ")

    def initialNames = List("0")

    def typeVariableIterator(types: List[String]): Iterator[Tree] =
      types.iterator.map(æ.apply)

    def termVariableIterator(names: List[String]): Iterator[Tree] =
      names.iterator.map(χ.apply)

    // System F has no dependent types.
    def typeIterator(depth: Int, types: List[String]): Iterator[Tree] =
      if (depth == 0) {
        typeVariableIterator(types)
      }
      else if (depth > 0) {
        typeVariableIterator(types) ++
        universalIterator(depth, types) ++
        functionArrowIterator(depth, types)
      }
      else
        sys error "plug depth negative."

    def universalIterator(depth: Int, types: List[String]):
        Iterator[Tree] = {
      val name = globalNameGenerator.next
      typeIterator(depth - 1, name :: types).map {
        body => ∀(name)(body)
      }
    }

    def functionArrowIterator(depth: Int, types: List[String]):
        Iterator[Tree] =
      for {
        domain <- typeIterator(depth - 1, types)
        range  <- typeIterator(depth - 1, types)
      } yield →(domain, range)

    def termIterator(
      depth: Int, names: List[String], types: List[String]
    ): Iterator[Tree] =
      if (depth == 0) {
        termVariableIterator(names)
      }
      else if (depth > 0) {
        termVariableIterator(names) ++
        typeAbstractionIterator(depth, names, types) ++
        instantiationIterator(depth, names, types) ++
        abstractionIterator(depth, names, types) ++
        applicationIterator(depth, names, types)
      }
      else
        sys error s"invert mode. secret code: Za Beastu!"

    def typeAbstractionIterator(
      depth: Int, names: List[String], types: List[String]
    ): Iterator[Tree] = {
      val newTypeVar = globalNameGenerator.next
      termIterator(depth - 1, names, newTypeVar :: types) map {
        body => Λ(newTypeVar, body)
      }
    }

    def instantiationIterator(
      depth: Int, names: List[String], types: List[String]
    ): Iterator[Tree] =
      for {
        term <- termIterator(depth - 1, names, types)
        typ  <- typeIterator(depth - 1, types)
      } yield □(term, typ)

    def abstractionIterator(
      depth: Int, names: List[String], types: List[String]
    ): Iterator[Tree] = {
      val x = globalNameGenerator.next
      for {
        note <- typeIterator(depth - 1, types)
        body <- termIterator(depth - 1, x :: names, types)
      } yield λ(x, note, body)
    }

    def applicationIterator(
      depth: Int, names: List[String], types: List[String]
    ): Iterator[Tree] =
      for {
        f <- termIterator(depth - 1, names, types)
        x <- termIterator(depth - 1, names, types)
      } yield ₋(f, x)
  }
}
