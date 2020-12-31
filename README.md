# Some straightforward proofs about inductive types in agda

It's all just stuff I've developed to aid my own understanding. There's a
file where W-Types are defined - for these see the HoTT book, or
'Constructive mathematics and computer programming' by Per Martin-Lof.
There I also define the natural numbers as a W-Type, and define addition
for these natural numbers, and then go through the motions of showing that
this definition of addition is correct - it's associative and commutative 
and behaves well with zero, one and the successor function. There's a file
where I prove that all initial N-algebras (in the sense of the HoTT book) 
can be identified, this also comes from the HoTT book, I use the machinery
of cubical agda to do this. There is also a file where I prove that W-Types
are initial W-algebras, this doesn't use any cubical machinery, but does
use function extensionality.

Sources I've used are:

The HoTT Book, available to read here: https://homotopytypetheory.org/book/
the relevant sections are from pages 154-160

Introduction to Univalent Foundations of Mathematics with Agda, here: 
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html

Libraries I've used are:

Type Topology, here: https://github.com/martinescardo/TypeTopology

Cubical, here: https://github.com/agda/cubical
