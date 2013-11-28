Related works, in the voice of System MF personified.

### Type reconstruction

#### Dimitrios Vytiniotis, Stephanie Weirich, Simon Peyton Jones:
     FPH: First-class polymorphism for Haskell:
     Declarative, constraint-free type inference for impredicative
     polymorphism

Most similarly motivated work ever! I wish my title could mention
"decidable" and "impredicative" in the same breath, too.
While their inference is decidable and complete, their type system
is not utterly impredicative. Sec 2.3 gives an example.

#### Barry Jay and Simon Peyton Jones: Scrap your type applications

Where I start from. I scrap type abstractions, too.

#### Didier Le Botlan and Didier Rémy: ML^F: Raising ML to the power of System F

[>80 citations.] Their impredicativity is bounded. I may be a different way of looking at ML^F. We share the motivating example `choose id`.

#### Didier Le Botlan and Didier Rémy: Recasting ML^F

... in precisely the opposite direction of myself! They argue that System F types are not good enough for ML^F, and I'm trying to be something where they are.

#### Martin Odersky and Konstantin Läufer: Putting Type Annotations to Work

[>90 citations.] They are predicative.

#### Frank Pfenning: Partial polymorphic type inference and higher-order unification

A (possibly nonterminating) algorithm to leave out even more type annotations. Worth a look!

#### Aleksy Schubert: Second-order unifcation and type inference for Church-style polymorphism

They say it's undecidable. I have to isolate the aspect of myself that makes their proof fail, or admit that I'm less expressive than System F. Otherwise, I can't be decidable either.

#### Mark P. Jones: First-class polymorphism with type inference

They convert nested quantifiers to prenex form. I enforce the opposite.

### Use of impredicativity in compilers

#### Yasohiko Minamide, Greg Morrisett, Robert Harper: Typed closure conversion

#### Philip Wadler and Stefen Blott: How to make ad-hoc polymorphism less ad hoc.
