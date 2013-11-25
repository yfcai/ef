trait Unification
extends MostGeneralSubstitution
   with SimplyTypedTerms
   with CanonicalNames
   with Pretty
{
  topLevel =>

  object Unification {
    private type Context = Map[Name, Type]

    private val ∅ : Context = Map.empty

    private[this]
    def singleton(p: (Name, Type)): Context = Map(p)

    private case class Typing(Γ : Context, τ : Type)

    // Precondition: All names are unique in the term.
    private class HindleysPrincipalTyping
    extends TermVisitor[Typing] {
      private[this] type T = Typing

      private[this] case class ID(index: Int) extends IDNumber

      private[this] val nameGenerator = new GenerativeNameGenerator(ID)

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
        val mgs = mostGeneralSubstitution(
          EqConstraint(f.τ, x.τ →: τ) :: unify(f.Γ, x.Γ))
        Typing(Γ mapValues (_ substitute mgs), τ substitute mgs)
      }
    }

    // The names in Γ2 are overriding
    private def unify(Γ1 : Context, Γ2 : Context): List[EqConstraint] =
      (Γ1.keySet & Γ2.keySet).map(
        x => EqConstraint(Γ1(x), Γ2(x))
      )(collection.breakOut)

    implicit class inferenceByUnificationOps(t: Term) {
      def infer: SimplyTypedTerm = inferFrom(∅)

      def inferFrom(Γ_global : PartialFunction[Name, Type]):
          SimplyTypedTerm = {
        val (canon, invFree, invBound) = t.canonize
        val Γ0 = (new HindleysPrincipalTyping)(canon).Γ
        val freeIDs = invFree.inverse
        val Γ = invFree flatMap { case (id, freeName) =>
          if (Γ_global isDefinedAt freeName)
            Map(id -> Γ_global(freeName))
          else
            Map.empty[Name, Type]
        }
        val mgs = mostGeneralSubstitution(unify(Γ0, Γ))
        SimplyTypedTerm(canon,
          (Γ0 ++ Γ) mapValues (_ substitute mgs),
          invFree ++ invBound)
      }

      def inferFrom[K <% Name, V <% Type](Γ : (K, V)*): SimplyTypedTerm =
        inferFrom(Γ.map({
          case (k, v) => (k: Name, v: Type)
        })(collection.breakOut): Map[Name, Type])
    }
  }
}

object TestUnification extends Unification {
  def main(args: Array[String]) {
    val Σ = χ("Σ")
    val ℤ = α("ℤ")
    val * = "List"
    val t = λ("x", "y") { Σ ₋ (Σ ₋ "x" ₋ "y") ₋ "z" } rename
      Map("y" -> "a", "z" -> "b") renameAll
      Map("x" -> "k", "b" -> "c") substitute
      ("y" -> χ("x"), "c" -> "k" ₋ "k1" ₋ "y")
    val τ = "r" →: ∀("r", "a" →: "r") →: ★(*, ℤ) →: ★(*, "r") renameAll
      Map("r" -> "α") substitute
      ("α" -> "β", "a" -> "α")
    val (c1, c2) = (τ.canonize, t.canonize)

    println(pretty(τ))
    println(pretty(c1._1))
    println((c1._2, c1._3))
    println()

    println(pretty(t))
    println(pretty(c2._1))
    println((c2._2, c2._3))
    println()

    val Γ : PartialFunction[Name, Type] = {
      // summation
      case name if name == Σ.name =>
        ℤ →: ℤ →: ℤ

      // integer literals
      case StringLiteral(name) if name matches "[0-9]+" =>
        ℤ
    }

    import Unification._
    println(pretty(t inferFrom Γ))
    println(pretty("f" ₋ "x" inferFrom ("f" -> ("ω" →: "β"))))
    println(pretty(λ("x")("x") ₋ "5" inferFrom Γ))
  }
}
