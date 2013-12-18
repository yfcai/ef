postulate + : ℤ → ℤ → ℤ

succ = λx : ℤ. + x 1

six = succ 5

id-α = λx : α. x

id = Λα. id-α

id-ℤ = id [ℤ]

zero = id [ℤ] 0

double = Λα. λf : α → α. λx : α. f (f x)

double-ℤ = double [ℤ]

double-ℤtoℤ = double [ℤ → ℤ]

seven = double [ℤ] (λx : ℤ. succ (succ x)) 3

self-app = λx : ∀α. α → α. x [∀β. β → β] x

quadruple = Λα. double [α → α] (double [α])


data List

postulate nil : ∀α. List α

postulate cons : ∀α. α → List α → List α

type Bool = ∀α. α → α → α

postulate isnil : ∀α. List α → Bool

postulate head : ∀α. List α → α

postulate tail : ∀α. List α → List α

postulate fix : ∀α. (α → α) → α


map =
  Λα β. λf : α → β.
    fix [List α → List β]
      (λmap-f : List α → List β. λxs : List α.
        isnil [α] xs [List β]
          (nil [β])
          (cons [β] (f (head [α] xs)) (map-f (tail [α] xs))))


map [ℤ] [ℤ] (quadruple [ℤ] (+ 1))
  (cons [ℤ] 1 (cons [ℤ] 2 (cons [ℤ] 3 (cons [ℤ] 4 (nil [ℤ])))))
