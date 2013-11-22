trait Unification
extends Substitution
   with TypedTerms
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

    private case class EqConstraint(lhs: Type, rhs: Type)

    // Precondition: All names are unique in the term.
    private class HindleysPrincipalTyping
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
        val mgs = findMGS(EqConstraint(f.τ, x.τ →: τ) :: unify(f.Γ, x.Γ))
        Typing(Γ mapValues (_ substitute mgs), τ substitute mgs)
      }
    }

    // The names in Γ2 are overriding
    private def unify(Γ1 : Context, Γ2 : Context): List[EqConstraint] =
      (Γ1.keySet & Γ2.keySet).map(
        x => EqConstraint(Γ1(x), Γ2(x))
      )(collection.breakOut)

    private def findMGS(constraints: List[EqConstraint]): Map[Name, Type] = {
      type Eq = EqConstraint
      val  Eq = EqConstraint
      constraints match {
        case Nil =>
          Map.empty

        case Eq(σ1 → τ1, σ2 → τ2) :: others =>
          findMGS(Eq(σ1, σ2) :: Eq(τ1, τ2) :: others)

        case Eq(★(f1, τ1), ★(f2, τ2)) :: others =>
          findMGS(Eq(f1, f2) :: Eq(τ1, τ2) :: others)

        case Eq(α(name1), α(name2)) :: others if name1 == name2 =>
          findMGS(others)

        case Eq(α(name), τ) :: others =>
          val mgs = findMGS(others map { case Eq(τ1, τ2) =>
            Eq(τ1 substitute (name -> τ), τ2 substitute (name -> τ))
          })
          val new_τ = τ substitute mgs
          if ((mgs contains name) && mgs(name) != new_τ)
            sys error s"Can't unify ${mgs(name)} = ${new_τ}"
          mgs.updated(name, new_τ)

        case Eq(τ, α(name)) :: others =>
            findMGS(Eq(α(name), τ) :: others)

        case Eq(τ1, τ2) :: others =>
          if (τ1 == τ2) findMGS(others)
          else sys error "Inconsistent equality constraints"
      }
    }

    implicit class inferenceByUnificationOps(t: Term) {
      def infer: TypedTerm = inferFrom(∅)
      def inferFrom(Γ : Context): TypedTerm = {
        val (canon, invFree, invBound) = t.canonize
        val Typing(_Γ, τ) = (new HindleysPrincipalTyping)(canon)
        val freeIDs = invFree.inverse
        val Γ0 = Γ map { case (k, v) => (freeIDs(k), v) }
        val mgs = findMGS(unify(_Γ, Γ0))
        // test that type variables fixed in Γ0 are never unified
        // to something else
        val fixedNames = (Γ map (p => getFreeNames(p._2))).
          fold(Set.empty[Name])(_ ++ _)
        mgs foreach { case (lhs, rhs) =>
          if (fixedNames contains lhs)
            sys error s"Can't unify fixed name $lhs = ${pretty(rhs)}"
        }
        TypedTerm(canon,
          (_Γ ++ Γ0) mapValues (_ substitute mgs),
          invFree ++ invBound)
      }
      def inferFrom[K <% Name, V <% Type](Γ : (K, V)*): TypedTerm =
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
    val Γ = Map(Σ.name -> (ℤ →: ℤ →: ℤ))
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

    import Unification._
    println(pretty(t inferFrom Γ))
    println(pretty("f" ₋ "x" inferFrom ("f" -> ("ω" →: "β"))))
  }
}
