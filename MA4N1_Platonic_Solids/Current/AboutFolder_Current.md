# About ./MA4N1_Platonic_Solids/Current/

This folder contains all of the finished lean files for the project

## File Breakdown 

### File1_SimpleGraphDefs.lean
This file contains basic graph theory structures such as $\verb+SimpGraph+$ and $\verb+FinGraph+$, and some simple definitions like the degree of a vertex and the neighbourhood of a vertex. The code in the file originated from $\verb+Simple_Graph_Theory.lean+$

### File2_DirectedEdgeHandshake.lean
This file contains definitions and lemmas required to prove the handshake lemma for directed edges. The code in this file originated from $\verb+Simple_Graph_Theory.lean+$

### File3_UndirectedEdgeHandshake.lean
This file contains definitions and lemmas required to prove the handshake lemma for undirected edges. The code in this file originated from $\verb+Undirected_Edges.lean+$

### File4_PlatonicGraphDefs.lean
This file contains structures, definition, and lemmas required to connect all of the graph theory to the inequality derivation. It contains the $\verb+PlatonicGraph+$ structure, an assumption about Euler's Characteristic Formula, and some lemmas that allow us to use the Handshake lemma defined in $\verb+File3+$ on PlatonicGraphs. The code in this file originated from $\verb+Simple_Graph_Theory.lean+$

### File5a_InequalityDerivationTheorem.lean
This file contains a theorem that states if we have a PlatonicGraph with $m>2$ and $n>2$, then we get $(m-2)*(n-2)<4$. The code in this file originated from $\verb+Inequality_Derivation_Theorem.lean+$

### File5b_InequalityDerivationLemmas.lean
This file contains lemmas that are required for the proof of the theorem in $\verb+File5a+$. They are separated into a different file to make the main theorem file cleaner and more focused. 
####
