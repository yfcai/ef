### Uses of impredicative polymorphism

- Really cool real-world case (abstract & concrete aspects)
  [http://stackoverflow.com/q/3076909](http://stackoverflow.com/a/3077295)
  [http://stackoverflow.com/q/8343239](http://stackoverflow.com/q/8343239)

- Church numbers as arguments:
  Prevent Church addition from adding non-numbers.

- ST Monad:
  Ensure the computation given to runST has no reference
  John Launchbury and Simon Peyton Jones: Lazy functional state threads.

- Boxes go bananas:
  Lam (Exp -> Exp) -- must ensure arg doens't inspect Exp!
  Solution: Only sound HOAS ADT has type (forall a. Exp a).
  Weirich and Washburnn: Boxes go bananas:
  Encoding HOAS with parametric polymorphism.

Seems to be making use of polymorphic functions not inspecting their
argument to delegate precondition verification to the compiler.

With higher-ranked types we can type functions that depends on functions
that depends on arguments not inspecting their arguments, and so forth.

About passing dictionaries: see related.md.
