succ = λx : ℤ. + x 1

six = succ 5

id = Λα. λx : α. x

id-ℤ = id [ℤ]

zero = id [ℤ] 0

double = Λα. λf : α → α. λx : α. f (f x)

double-ℤ = double [ℤ]

double-ℤtoℤ = double [ℤ → ℤ]

seven = double [ℤ] (λx : ℤ. succ (succ x)) 3

self-app = λx : ∀α. α → α. x [∀β. β → β] x

quadruple = Λα. double [α → α] (double [α])

nil : ∀α. List α

cons : ∀α. α → List α → List α

isnil : ∀α. List α → Bool

head : ∀α. List α → α

tail : ∀α. List α → List α

. todo: nice step -through semantics
fix : ∀α. (α → α) → α

map =
  Λα β. λf : α → β.
    fix [List α → List β]
      (λmap-f : List α → List β. λxs : List α.
        isnil [α] xs [List β]
          (nil [β])
          (cons [β] (f (head [α] xs)) (map-f (tail [α] xs))))


map [ℤ] [ℤ] (quadruple [ℤ] (+ 1))
  (cons [ℤ] 1 (cons [ℤ] 2 (cons [ℤ] 3 (cons [ℤ] 4 (nil [ℤ])))))
