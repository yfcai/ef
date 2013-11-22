trait Unification extends Substitution with TypedTerms with CanonicalNames {
  topLevel =>

  object Unification {
    type Context = Map[Name, Type]

    val ∅ : Context = Map.empty

    private[this]
    def singleton(p: (Name, Type)): Context = Map(p)

    case class Typing(Γ : Context, τ : Type)

    case class EqConstraint(lhs: Type, rhs: Type)

    // Precondition: All names are unique in the term.
    class HindleysPrincipalTypings
    extends TermVisitor[Typing] {
      private[this] type T = Typing

      private[this] val nameGenerator = new GenerativeNameGenerator

      def newTypeVar: Type = topLevel.α(nameGenerator.next)

      def χ(x: Name): T = {
        val α = newTypeVar
        Typing(singleton(x -> α), α)
      }

      def λ(x: Name, body: T): T = {
        val σ = body.Γ.applyOrElse[Name, Type](x, _ => newTypeVar)
        Typing(body.Γ, σ →: body.τ)
        // Note that we don't remove x from body.Γ.
        // body.Γ(x) is the type argument of this λ.
        // For the context to be meaningful in this way,
        // we require all names---even bound ones---be unique.
      }

      def ε(f: T, x: T): T = {
        val τ = newTypeVar
        val Γ = f.Γ ++ x.Γ
        val mgs = findMostGeneralSubstitution(
          EqConstraint(f.τ, x.τ →: τ) :: ((f.Γ.keySet & x.Γ.keySet).map(
            y => EqConstraint(f.Γ(y), x.Γ(y))
          )(collection.breakOut): List[EqConstraint]))
        Typing(Γ mapValues (_ substitute mgs), τ substitute mgs)
      }

      def ϕ(value: Int): T = Typing(∅, ℤ)
      def Σ : T = Typing(∅, ℤ →: ℤ →: ℤ)
    }

    def findMostGeneralSubstitution(constraints: List[EqConstraint]):
        Map[Name, Type] = {
      type Eq = EqConstraint
      val  Eq = EqConstraint
      constraints match {
        case Nil =>
          Map.empty

        case Eq(σ1 → τ1, σ2 → τ2) :: others =>
          findMostGeneralSubstitution(Eq(σ1, σ2) :: Eq(τ1, τ2) :: others)

        case Eq(α(name), τ) :: others =>
          val mgs =
            findMostGeneralSubstitution(others map { case Eq(τ1, τ2) =>
              Eq(τ1 substitute (name -> τ), τ2 substitute (name -> τ))
            })
          mgs.updated(name, τ substitute mgs)

        case Eq(τ, α(name)) :: others =>
          findMostGeneralSubstitution(Eq(α(name), τ) :: others)

        case Eq(τ1, τ2) :: others =>
          if (τ1 == τ2) findMostGeneralSubstitution(others)
          else sys error "Inconsistent equality constraints"
      }
    }

    def infer(t: Term): TypedTerm = {
      val (canon, invFree, invBound) = t.canonize
      val Typing(_Γ, τ) = (new HindleysPrincipalTypings)(canon)
      TypedTerm(canon, _Γ, invFree ++ invBound)
    }
  }
}

object TestUnification extends Unification with Pretty {
  def main(args: Array[String]) {
    val t = λ("x", "y") { Σ ₋ (Σ ₋ "x" ₋ "y") ₋ "z" } rename
      Map("y" -> "a", "z" -> "b") renameAll
      Map("x" -> "k", "b" -> "c") substitute
      ("y" -> χ("x"), "c" -> "k" ₋ "k1" ₋ "y")
    val τ = "r" →: ∀("r", "a" →: "r") →: ℤ →: "r" renameAll
      Map("r" -> "α") substitute
      ("α" -> "β", "a" -> "α")
    val (c1, c2) = (τ.canonize, t.canonize)

    println(pretty(τ))
    println(pretty(c1._1))
    println((c1._2, c1._3))

    println(pretty(t))
    println(pretty(c2._1))
    println((c2._2, c2._3))
    println(pretty(Unification infer t))
  }
}
