Existential F
-------------

Iteration 3: incorporate HML and McBride's Not-a-Number

HML gives flexible constraints. Combined with true existential
types, they should provide a compositional solution in deciding
whether to capture any Skolem/anti-Skolem on each application.

"I am not a number, I am a free variable" is a functional pearl
about the syntax trees of Epigram. Our previous generative name
binding language suffers from hidden binder aliasing and makes
it difficult to add data variants. In the next reimplementation,
we shall use the Not-a-Number idea to solve the expression
problem with reduced boilerplates, by sacrificing static type
safety in all operations on syntax trees. We shall retain
dynamic type safety, however: Every syntax tree node will be
checked for type correctness as soon as it is created.
