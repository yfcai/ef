. System F examples for Mac & Linux

succ = λx : ℤ. + x 1

six = succ 5

id = Λα. λx : α. x

id-int = id [ℤ]

id [ℤ] 0

double = Λα. λf : α → α. λx : α. f (f x)

double-int = double [ℤ]

double-int->int = double [ℤ → ℤ]

seven = double [ℤ] (λx : ℤ. succ (succ x)) 3

self-app = λx : ∀α. α → α. x [∀β. β → β] x

quadruple = Λα. double [α → α] (double [α])

nil

cons

isnil

head

tail

map : ∀α β. (α → β) → List α → List β
map = Λα β. λf : α → β. λxs : List α.
        isnil [α] xs [List β]
          (nil [β])
          (cons [β] (f (head [α] xs))
                    (map [α] [β] f (tail [α] xs)))

map [ℤ] [ℤ]
  (quadruple [ℤ] (+ 1))
  (cons [ℤ] 1 (cons [ℤ] 2 (cons [ℤ] 3 (cons [ℤ] 4 (nil [ℤ])))))

. Church encoding

type CBool = ∀α. α → α → α

tru : CBool
tru = Λα. λthen : α. λelse : α. then

fls : CBool
fls = Λα. λthen : α. λelse : α. else

not : CBool → CBool
not = λb : CBool. Λα. λthen : α. λelse : α. b [α] else then

type CNat = ∀α. (α → α) → α → α

c₀ : CNat
c₀ = Λα. λs : α → α. λz : α. z

c₁ : CNat
c₁ = Λα. λs : α → α. λz : α. s z

c₂ : CNat
c₂ = Λα. λs : α → α. λz : α. s (s z)

csucc : CNat → CNat
csucc = λn : CNat. Λα. λs : α → α. λz : α. s (n [α] s z)

c+ : CNat → CNat → CNat
c+ = λm : CNat. λn : CNat. m [CNat] csucc n

c+' : CNat → CNat → CNat
c+' = λm : CNat. λn : CNat.
         Λα. λs : α → α. λz : α. m [α] s (n [α] s z)

c* : CNat → CNat → CNat
c* = λm : CNat. λn : CNat. m [CNat] (c+ n) c₀

c*' : CNat → CNat → CNat
c*' = λm : CNat. λn : CNat. Λα. λs : α → α.
  . λx : α.
  n [α] (m [α] s)
  .               x

c^ : CNat → CNat → CNat
c^ = λm : CNat. λn : CNat. n [CNat] (c* m) c₁

c^' : CNat → CNat → CNat
c^' = λm : CNat. λn : CNat. Λα. n [α → α] (m [α])

cnat-to-int : CNat → ℤ
cnat-to-int = λn : CNat. n [ℤ] (+ 1) 0

cnat-to-int (csucc (csucc (csucc (csucc c₀))))

. rant

  Exercises by Pierce:

  23.4.1 Write typing derivations... judge for yourself which one.

  23.4.3 Write `reverse : ∀α. List α → List α`.

  23.4.4 Write a simple polymorphic sorting algorithm
         `sort : ∀α. (α → α → Bool) → List α → List α`
         where the first argument is a comparison function
         for elements of type α.

  23.4.5 Write `and : CBool → CBool → CBool`

  23.4.6 Write `iszero` that will return `tru` when applied
         to the Church numeral `c₀` and `fls` otherwise.

  23.4.7 Give an informal argument that `c*'` and `c^'`
         implement the arithmetic multiplication and
         exponentiation operators.

  23.4.9 Use an encoding of pairs of naturals to write the
         predecessor function.

  23.4.A `vpred = λn. λs. λz. n (λp. λq. q (p s)) (k z) i`
         Add type annotation to this term so that it has
         type `CNat → CNat.` Extra credit: explain how it works.
