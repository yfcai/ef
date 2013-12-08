...
For conjunctive functors, we can put quantifiers inside
or outside functor argument at will.
...

data Pair

data ℤ

data Name

postulate george : Name

postulate pair : ∀α β. α → β → Pair α β

postulate π₁ : ∀α β. Pair α β → α

postulate π₂ : ∀α β. Pair α β → β

postulate p1 : ∀α. Pair (α → α) α

postulate p2 : Pair (∀α. α → α) (∀α. α)

p1-to-p2 =
  λp1 : ∀α. Pair (α → α) α. pair [∀α. α → α] [∀α. α]
    (Λα. π₁ [α → α] [α] (p1 [α]))
    (Λα. π₂ [α → α] [α] (p1 [α]))

p1

p1-to-p2 p1

p2-to-p1 =
  λp2 : Pair (∀α. α → α) (∀α. α). Λα. pair [α → α] [α]
    (π₁ [∀α. α → α] [∀α. α] p2 [α])
    (π₂ [∀α. α → α] [∀α. α] p2 [α])

p2

p2-to-p1 p2

...
Counterintuitively, we can also swap quantifiers in and
out of arguments of disjunctive functors. In classical
logic, we have (∀α. σ) ∨ (∀α. τ) → (∀α. σ ∨ τ) without
the converse, because (∀α. σ ∨ τ) may hold sometimes
for σ and sometimes for τ. Why we can write something
like `s1-to-s2` is beyond me.
...

data Either

postulate inj₁ : ∀α β. α → Either α β

postulate inj₂ : ∀α β. β → Either α β

postulate either : ∀α β γ. (α → γ) → (β → γ) → Either α β → γ

postulate s1 : ∀α. Either (α → α) α

postulate s2 : Either (∀α. α → α) (∀α. α)

s1-to-s2 =
  λs1 : ∀α. Either (α → α) α.
    either [α → α] [α] [Either (∀α. α → α) (∀α. α)]
      (λx : α → α. inj₁ [∀α. α → α] [∀α. α] (Λα. x))
      (λy : α    . inj₂ [∀α. α → α] [∀α. α] (Λα. y))
      (s1 [α])

s1

s1-to-s2 s1

s2-to-s1 =
  λs2 : Either (∀α. α → α) (∀α. α).
    Λα. either [∀α. α → α] [∀α. α] [Either (α → α) α]
      (λx : ∀α. α → α. inj₁ [α → α] [α] (x [α]))
      (λy : ∀α. α    . inj₂ [α → α] [α] (y [α]))
      s2

s2

s2-to-s1

...
What about contravariant functors?
Universal quantifiers turn into existentials and vice versa.
...

data Contra

postulate contra : ∀α. (α → ℤ) → Contra α

postulate decontra : ∀α. Contra α → α → ℤ

postulate c1 : ∀α. Contra (α → α)

contra-outside-in =
  Λα. λc : Contra (α → α).
    contra [∀α. α → α] (λx : ∀α. α → α. decontra [α → α] c (x [α]))

c1

contra-outside-in [α] (c1 [α])

contra-inside-out =
  λf : Contra (∀α. α → α) → Name.
    Λα. λc : Contra (α → α). f (contra-outside-in [α] c)

...
What about invariant functors?
They seem very much rigid.
...

data Invariant

postulate box : ∀α. (α → α) → Invariant α

postulate unbox : ∀α. Invariant α → (α → α)

invariant-inside-out =
  λi : Invariant (∀α. α).
    unbox [∀α. α] i

invariant-outside-in =
  λi : ∀α. Invariant (α → α).
    Λα. unbox [α → α] (i [α])