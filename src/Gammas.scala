// A Gamma consists of all bound type names,
// a typing function for free variables,
// and a map for bound variables.
trait Gammas extends Unification {
  trait Γ {
    def typevars: Set[Type.FreeName[Type]]
    def termvars: Map[λ, Type]
    def freevars: PartialFunction[ξ, Type]

    def ⊢ (t: Term): Type

    implicit class UnparseTermInTypingContext(t: Term) {
      def unparse: String = ChurchTerm(t, termvars).unparse
    }
  }

  case class Γ_EF(
    typevars: Set[Type.FreeName[Type]],
    termvars: Map[λ, Type],
    freevars: PartialFunction[ξ, Type]
  ) extends Γ {
    Γ =>

    def ⊢ (t0: Term): Type = t0 match {
      // (TAUT)
      case χ(x) =>
        termvars(x)

      case x: ξ if freevars isDefinedAt x =>
        freevars(x)

      // (ascription)
      // in EF, ascription is a syntactic sugar.
      // (t : τ) can be written as ((λx : τ. x) t).
      case Ξ(t, τ_ascribed) =>
        val id = λ { x => x }
        val desugared = id ₋ t
        Γ_EF(typevars,
             termvars updated (id, τ_ascribed),
             freevars) ⊢ desugared

      // (∀I)
      // oh dear, let's hope we managed to get rid of it.
      //case Λ(a, body) =>
      //  ∀(a)(Γ ⊢ body)

      // (→∀I)
      case x @ λ(_, body) =>
        val σ = termvars(x)
        val toQuantify = σ.freeNames -- typevars
        val τ = Γ_EF(typevars ++ toQuantify, termvars, freevars) ⊢ body
        ∀(toQuantify, σ →: τ)

      // (→∀∃E)
      case s ₋ t =>
        val funType = Γ ⊢ s
        val argType = Γ ⊢ t
        getResultTypeOfApplication(funType, argType)

      case _ =>
        TypeError { s"${t0.unparse} is not a typeable construct" }
    }
  }

  // consider putting methods of this object in a trait.
  object Γ_ℤ extends ℤ_Ring {
    def ⊢ (c: ChurchTerm): Type = Γ_ℤ(c) ⊢ c.term

    def apply(c: ChurchTerm): Γ_EF =
      Γ_EF(Set(ℤ), c.annotations, ℤ_lit_arith)

    def apply(m: Module): Γ_EF = {
      val synonyms = m.resolveSynonyms
      val signatures = synonyms resolve m.signatures
      def mkEF(notes: Map[λ, Type], defs: Map[ξ, Type]) =
        Γ_EF(Set(ℤ), notes, signatures ++ defs orElse ℤ_lit_arith)
      val (notes, defs) = m.linearizedDefinitions.
        foldLeft[(Map[λ, Type], Map[ξ, Type])]((Map.empty, Map.empty)) {
          case ((notes, defs), (name, ChurchTerm(t, oldNotes))) => try {
            val church = ChurchTerm(t, synonyms resolve oldNotes)
            val newNotes = resolveLetBindings(church, x => mkEF(x, defs))
            assert((newNotes find (notes contains _._1)) == None)
            val accumulatedNotes = notes ++ newNotes
            val τ = mkEF(newNotes, defs) ⊢ t
            if (signatures contains name) {
              PrenexForm(τ) ⊑? PrenexForm(signatures(name)) match {
                case Success(_) => ()
                case Failure(s) => TypeError {
                  s"""|incompatible signature.
                      |declared:  ${signatures(name).unparse}
                      |actual:    ${τ.unparse}
                      |due to
                      |$s
                      |""".stripMargin
                }
              }
              (accumulatedNotes, defs)
            }
            else
              (accumulatedNotes, defs updated (name, τ))
          } catch {
            case e: TypeError => TypeError {
              "TYPE ERROR IN PARAGRAPH\n" +
              s"${m.filename}:${m lineNumber name}" +
              e.message
            }
          }
        }
      // sanity check
      (synonyms.toMap.toList ++ signatures ++ defs) foreach {
        case (name0, τ) => τ.freeNames foreach {
          case name: δ if name != ℤ && ! (synonyms.toMap contains name) =>
            TypeError {
              s"""|TYPE ERROR IN PARAGRAPH
                  |${m.filename}:${m lineNumber name0}
                  |unknown type name ${name.name}"
                  |""".stripMargin
            }
          case _ => ()
        }
      }
      mkEF(notes, defs)
    }

    def resolveLetBindings(c: ChurchTerm, Γ: Map[λ, Type] => Γ):
        Map[λ, Type] =
      c.term.traverse.foldLeft(c.annotations) {
        case (notes, (abs: λ) ₋ dfn)
            if notes(abs) == UnknownType =>
          notes updated (abs, Γ(notes) ⊢ dfn)
        case (notes, _) =>
          notes
      }

    def resolveLetBindings(m: Module): (Γ, Module) = {
      val Γ = Γ_ℤ(m)
      (Γ, m.definitions.foldRight(m) {
        case ((x, xdef), module) =>
          module.setDefinition(x, ChurchTerm(xdef.term, Γ.termvars))
      })
    }

  }

  trait ℤ_Ring {
    val ℤ = δ("ℤ")

    val ℤ_literal = """(-)?\d+"""

    val ℤ_lit_arith: PartialFunction[ξ, Type] = {
      case ξ(s) if s matches ℤ_literal =>
        ℤ

      case ξ("+") | ξ("-") | ξ("*") | ξ("/") =>
        ℤ →: ℤ →: ℤ

      // undefined
      case ξ("???") =>
        ∀("a̧") { a => a } // broken a for "absurd"
    }
  }
}
