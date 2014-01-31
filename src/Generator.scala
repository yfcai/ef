object Generator extends ProgramGenerator {
  def commands =
    """|        generate launch program generator
       |
       |        canonize unify names, erase to Church-style
       |
       |        filter   filter lines of terms by a hard-coded
       |                 predicate
       |""".stripMargin


  def dispatch: PartialFunction[(String, Array[String]), Unit] = {
    case ("generate", args) =>
      generate(args)

    case ("canonize", args) =>
      canonize(args)

    case ("ignoreTabs", _) =>
      ignoreTabsInStdin()

    case ("filter", args) => args.head match {
      // filter out those untypeable in Cuit
      case "untypeable" =>
        filterUntypeable()

      case "typeable" =>
        filterTypeable()

      case "depth" =>
        filterDepth(args.tail.head.toInt)
    }
  }

  def generate(args: Array[String]) {
    val choice = args.head
    val n = args.tail.head.toInt
    (choice match {
      case "F"      => WellTypedF
      case "Church" => Church
      case "Local"  => Local
    }).run(n)
  }

  def canonize(args: Array[String]): Unit = {
    io.Source.stdin.getLines.foreach { line =>
      if (! line.isEmpty) ParagraphExpr(line) match {
        case Signature(_, _) =>
          ()

        case Definition(x, t) =>
          if (! args.isEmpty && args.head == "erase")
            println(canonize(t).unparse)
          else
            println(s"$x = ${canonize(t).unparse}")

        case NakedExpression(e) =>
          println(canonize(e).unparse)
      }
    }
  }

  def filterUntypeable() {
    val typing = new Cuit.OrderlessTyping(Cuit.Module.empty)
    import typing._
    io.Source.stdin.getLines.foreach { line =>
      val t = Cuit.Term(line)
      typeError(Cuit.ignoreTabs(t)) match {
        case None => ()
        case Some(_) => println(line)
      }
    }
  }

  def filterTypeable() {
    val typing = new Cuit.OrderlessTyping(Cuit.Module.empty)
    import typing._
    io.Source.stdin.getLines.foreach { line =>
      val t = Cuit.Term(line)
      typeError(Cuit.ignoreTabs(t)) match {
        case None => println(line)
        case Some(_) => ()
      }
    }
  }

  def filterDepth(threshold: Int) {
    io.Source.stdin.getLines.foreach { line =>
      if (F.depth(F.Term(line)) <= threshold)
        println(line)
    }
  }

  def ignoreTabsInStdin(): Unit =
    io.Source.stdin.getLines.foreach { line =>
      println(F.ignoreTabs(F.Term(line)).unparse)
    }

  // todo: rename.
  type UnorderedImpredicativeTypes = SecondOrderOrderlessTypes

  object F extends SystemF with IgnoreTypeAbstractions
  object Cuit extends UnorderedImpredicativeTypes with IgnoreTypeAbstractions
}

trait IgnoreTypeAbstractions extends Syntax {
  def ignoreTabs(t: Tree): Tree = t match {
    case ∙(_, _) => t
    case Λ(_, body) => ignoreTabs(body)
    case τ if τ.tag.genus == Type => τ
    case ⊹(tag, children @ _*) => ⊹(tag, children.map(ignoreTabs): _*)
  }

  def depth(t: Tree): Int = t match {
    case ∙(_, _) => 0
    case ⊹(Universal, _, _, body) => 1 + depth(body)
    case ⊹(_, children @ _*) => 1 + children.map(depth).max
  }
}

trait ProgramGenerator extends Modules {
  object WellTypedF extends WellTypedF

  object Church extends LocalGenerator {
    def termRecursion(
      depth: Int, names: Map[String, Tree], types: List[String]
    ): Iterator[Tree] = {
      typeAbstractionIterator(depth, names, types) ++
      abstractionIterator(depth, names, types) ++
      applicationIterator(depth, names, types)
    }

    def operatorPredicate: Tree => Boolean =
      _.preorder.find(_.tag == FunctionArrow) != None
  }

  object Local extends LocalGenerator {
    def termRecursion(
      depth: Int, names: Map[String, Tree], types: List[String]
    ): Iterator[Tree] = {
      typeAbstractionIterator(depth, names, types) ++
      instantiationIterator(depth, names, types) ++
      abstractionIterator(depth, names, types) ++
      applicationIterator(depth, names, types)
    }

    def operatorPredicate: Tree => Boolean = _.tag == FunctionArrow
  }

  // convert term to canonical form
  //
  // 1. instantiations are discarded
  //
  // 2. on chained type abstractions, the specs are sorted by index
  //    and rebound
  def canonize(t: Tree,
    gen: GlobalNameGenerator,
    gen2: GlobalNameGenerator): Tree = t match {
    case t @ ∙(_, _) =>
      t
    case λ(x, note, body) =>
      val y = gen2.next
      λ(y,
        canonize(note, gen, gen2),
        canonize(body, gen, gen2).subst(χ(x), χ(y)))
    case f ₋ x =>
      ₋(canonize(f, gen, gen2), canonize(x, gen, gen2))
    case t □ τ =>
      canonize(t, gen, gen2)
    case σ → τ =>
      →(canonize(σ, gen, gen2), canonize(τ, gen, gen2))
    case t if t.tag == TypeAbstraction || t.tag == Universal =>
      val binder = t.tag.asInstanceOf[Binder]
      val (specs, body) = t.unbindAll(binder)
      val oldNames = specs.map(spec =>
        (spec.x, body.preorder.indexOf(æ(spec.x)))).sortBy(_._2).map(_._1)
      val newNames = oldNames.map(_ => gen.next)
      val lexicon  = oldNames.zip(newNames).map({
        case (oldName, newName) => (oldName, æ(newName))
      })(collection.breakOut): Map[String, Tree]

      newNames.foldRight(canonize(body, gen, gen2) subst lexicon) {
        case (α, body) => binder match {
          case Universal => ∀(α, Annotation.none(), body)
          case TypeAbstraction => Λ(α, body)
        }
      }
  }

  def canonize(t: Tree): Tree =
    canonize(t,
      new GlobalNameGenerator("T"),
      new GlobalNameGenerator("x"))

  trait Generator {
    def generate(depth: Int): Unit

    def run(n: Int) { termName.reset ; typeName.reset ; generate(n) }
    val termName = new GlobalNameGenerator("x")
    val typeName = new GlobalNameGenerator("T")
  }

  trait UntypedGenerator extends Generator {
    def withDepthLimit(n: Int): Iterator[Tree]

    def generate(depth: Int): Unit =
      withDepthLimit(depth).foreach(t => println(t.unparse))
  }

  trait TypedGenerator extends Generator {
    def withDepthLimit(depth: Int): Search

    def generate(depth: Int): Unit = {
      val name = new GlobalNameGenerator("t")
      withDepthLimit(depth).foreach({
        case Domain(t, τ) =>
          val x = name.next
          println(s"$x : ${τ.unparse}\n$x = ${t.unparse}\n")
      })
    }

    type Search = Iterator[Domain]

    case class Domain(t: Tree, τ: Tree) {
      def apply(f: Tree => Tree, μ: Tree => Tree):
          Domain = Domain(f(t), μ(τ))
    }

    object Domain extends (((String, Tree)) => Domain) {
      def apply(p: (String, Tree)): Domain =
        Domain(χ(p._1), p._2)
    }
  }

  trait SystemFTypes extends Generator {
    type Gamma     = Map[String, Tree]
    type Delta     = List[String]
    type Predicate = Tree => Boolean
    type Result    = Iterator[Tree]

    val Γ0: Gamma = Map.empty
    val Δ0: Delta = Nil
    val P0: Predicate = _ => true

    def typeIterator(depth: Int, Δ: Delta): Iterator[Tree] =
      if (depth == 0) {
        typeVariableIterator(Δ)
      }
      else if (depth > 0) {
        typeVariableIterator(Δ) ++
        universalIterator(depth, Δ) ++
        functionArrowIterator(depth, Δ)
      }
      else
        sys error "plug depth negative."

    def typeVariableIterator(Δ: Delta): Iterator[Tree] =
      Δ.iterator.map(æ.apply)

    def universalIterator(depth: Int, Δ: Delta):
        Iterator[Tree] = {
      val name = typeName.next
      typeIterator(depth - 1, name :: Δ).map {
        body => ∀(name)(body)
      }
    }

    def functionArrowIterator(depth: Int, Δ: Delta):
        Iterator[Tree] =
      for {
        domain <- typeIterator(depth - 1, Δ)
        range  <- typeIterator(depth - 1, Δ)
      } yield →(domain, range)
  }

  trait NonsuperfluousFTypes extends Generator {
    type Gamma     = Map[String, Tree]
    type Delta     = List[String]
    type Predicate = Tree => Boolean
    type Result    = Iterator[Tree]

    val Γ0: Gamma = Map.empty
    val Δ0: Delta = Nil
    val P0: Predicate = _ => true

    def typeIterator(depth: Int, Δ: Delta, P: Predicate = P0):
        Iterator[Tree] =
      if (depth == 0) {
        typeVariableIterator(Δ)
      }
      else if (depth > 0) {
        typeVariableIterator(Δ) ++
        universalIterator(depth, Δ, P) ++
        functionArrowIterator(depth, Δ, P)
      }
      else
        sys error "plug depth negative."

    def typeVariableIterator(Δ: Delta):
        Iterator[Tree] =
      Δ.iterator.map(æ.apply)

    def universalIterator(depth: Int, Δ: Delta, P: Predicate):
        Iterator[Tree] = {
      val α = typeName.next
      val f = (τ: Tree) => ∀(α)(τ)
      typeIterator(depth - 1, α :: Δ).
        withFilter(τ => τ.freeNames.contains(α) && P(f(τ))).
        map(f)
    }

    def functionArrowIterator(depth: Int, Δ: Delta, P: Predicate):
        Iterator[Tree] =
      for {
        domain <- typeIterator(depth - 1, Δ, P)
        range  <- typeIterator(depth - 1, Δ, P)
      } yield →(domain, range)
  }

  trait LocalGenerator extends UntypedGenerator with SystemFTypes {
    def termRecursion(depth: Int, Γ: Gamma, Δ: Delta): Iterator[Tree]

    // we don't reset global name generator, ever.
    // worst case scenario: 9-character name (xFFFFFFFF).
    def withDepthLimit(depth: Int): Iterator[Tree] =
      termIterator(depth, Map.empty, Nil)

    def termVariableIterator(Γ: Gamma, π: Predicate): Iterator[Tree] =
      Γ.iterator.filter(p => π(p._2)).map(χ apply _._1)

    def termIterator(depth: Int, Γ: Gamma, Δ: Delta, π: Predicate = P0):
        Iterator[Tree] = {
      if (depth == 0)
        termVariableIterator(Γ, π)
      else if (depth > 0)
        termVariableIterator(Γ, π) ++
          termRecursion(depth, Γ, Δ)
      else
        sys error s"invert mode. secret code: Za Beastu!"
    }

    def typeAbstractionIterator(depth: Int, Γ: Gamma, Δ: Delta):
        Iterator[Tree] = {
      val newTypeVar = typeName.next
      termIterator(depth - 1, Γ, newTypeVar :: Δ) map {
        body => Λ(newTypeVar, body)
      }
    }

    def instantiatedPredicate: Predicate =
      _.tag == Universal

    def instantiationIterator(depth: Int, Γ: Gamma, Δ: Delta):
        Iterator[Tree] =
      for {
        term <- termIterator(depth - 1, Γ, Δ, instantiatedPredicate)
        typ  <- typeIterator(depth - 1, Δ)
      } yield □(term, typ)

    def abstractionIterator(depth: Int, Γ: Gamma, Δ: Delta):
        Iterator[Tree] = {
      val x = termName.next
      for {
        note <- typeIterator(depth - 1, Δ)
        gamma = Γ.updated(x, note)
        body <- termIterator(depth - 1, gamma, Δ)
      } yield λ(x, note, body)
    }

    def operatorPredicate: Predicate

    def applicationIterator(depth: Int, Γ: Gamma, Δ: Delta):
        Iterator[Tree] =
      for {
        f <- termIterator(depth - 1, Γ, Δ, operatorPredicate)
        x <- termIterator(depth - 1, Γ, Δ)
      } yield ₋(f, x)
  }

  trait WellTypedF extends TypedGenerator with NonsuperfluousFTypes {
    def withDepthLimit(depth: Int): Search =
      term(depth, Γ0, Δ0, P0)

    def term(depth: Int, Γ: Gamma, Δ: Delta, P: Predicate): Search =
      termVariable(Γ, P) ++ (depth match {
        case 0 =>
          Iterator.empty
        case n if n > 0 =>
          typeAbstraction(depth, Γ, Δ, P) ++
          instantiation(depth, Γ, Δ, P) ++
          abstraction(depth, Γ, Δ, P) ++
          application(depth, Γ, Δ, P)
        case n if n < 0 =>
          sys error "losing humanity..."
      })

    def termVariable(Γ: Gamma, P: Predicate): Search =
      Γ.iterator.filter(p => P(p._2)).map(Domain)

    def typeAbstraction(depth: Int, Γ: Gamma, Δ: Delta, P: Predicate):
        Search = {
      val α = typeName.next
      val f = (t: Tree) => Λ(α, t)
      val μ = (τ: Tree) => ∀(α)(τ)
      val Q = (τ: Tree) => τ.freeNames.contains(α) && P(μ(τ))
      term(depth - 1, Γ, α :: Δ, Q).map(_(f, μ))
    }

    def instantiation(depth: Int, Γ: Gamma, Δ: Delta, P: Predicate):
        Search =
      for {
        σ <- typeIterator(depth - 1, Δ)
        q = (τ: Tree) => τ.tag == Universal && P(τ(σ))
        d <- term(depth - 1, Γ, Δ, q)
      } yield Domain(d.t, d.τ(σ))

    def abstraction(depth: Int, Γ: Gamma, Δ: Delta, P: Predicate):
        Search = {
      val x  = termName.next
      for {
        σ <- typeIterator(depth - 1, Δ)
        f = (t: Tree) => λ(x, σ, t)
        μ = (τ: Tree) => →(σ, τ)
        d <- term(depth - 1, Γ.updated(x, σ), Δ, τ => P(μ(τ)))
      } yield Domain(f(d.t), μ(d.τ))
    }

    def application(depth: Int, Γ: Gamma, Δ: Delta, P: Predicate):
        Search = {
      val p = (τ: Tree) => τ.tag == FunctionArrow && P(τ.children.last)
      for {
        f <- term(depth - 1, Γ, Δ, p)
        q = (τ: Tree) => τ α_equiv f.τ.children.head
        x <- term(depth - 1, Γ, Δ, q)
      } yield Domain(₋(f.t, x.t), f.τ.children.last)
    }
  }
}
