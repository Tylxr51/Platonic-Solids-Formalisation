# About ./MA4N1_Platonic_Solids/Old/

We decided to keep all of our original working files in for two reasons:
- 1. They're convienient to refer back to when stuff breaks
- 2. They show some failed attempts / foundational work that guided the work found in Current.

## File Breakdown:
### Definitions.lean *(Sean)*
This file just contains our original definition of a platonic solids. This was where we realised that making rigorous and precise definitions in Lean was quite difficult, and we should probably pivot to an area with more concrete and easily formalisable definitions - graph theory
### Inequality_Derivation_Theorem.lean *(Tyler)*
This contains the derivation of $(m-2)*(n-2)<4$ where all of the variables are just abstract things and have no relation to any actual definitions. This was very helpful, because it meant that when we did actually have proper definitions and theorems, we could just plug them in and it all worked out nicely :)
### Simple_Graph_Theory.lean *(Sean)*
This contains all of the definitions about simple graphs and directed edges and builds up to deriving the handshake lemma, $nV=2E$, for directed edges. This provided the foundation to proving the undirected version.
### Undirected_Edges.lean *(Elliot)*
This contains all of the lemmas and definitions building up to deriving the handshake lemma for undirected edges. This completes the derivation of our main theorem, as $mF=2E$ and $V-E+F=2$ are build from assumptions, whereas this is built from the ground up.