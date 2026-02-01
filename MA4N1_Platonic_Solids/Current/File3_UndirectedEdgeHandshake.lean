import Mathlib.Data.Sym.Sym2
import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
import MA4N1_Platonic_Solids.Current.File2_DirectedEdgeHandshake

-- We currently count directed edges as ordered pairs. We now want an undirected edge set.
-- That is, instead of DirEdgeSet = {(u,v) | G.adj u v}, we have EdgeSet = {{u,v} | G.adj uv}
-- So we want to identfy (u,v) and (v,u) to be the same, so I will attempt to create a quotient map.


-- To define functions around these edges, it might be best to repurpose the definition to suit
-- our needs. This give us a term (edge) 'e' consisting of the pair (u,v) (given by e.1) and a proof
-- that adj u v (given by e.2)
def DirEdge {VertSet : Type*} (G : SimpGraph VertSet) :
    Type _ := {e: VertSet × VertSet // G.adj e.1 e.2}
-- Though conceptually the same as DirEdgeset, I expect this to be easier for working with functions
-- especially considering it encodes a pair (a vertices pair and their proof of adjacency)
def VertSet_to_Sym2 {VertSet : Type*} (G : SimpGraph VertSet) :
    DirEdge G → Sym2 VertSet := fun e => Sym2.mk e.1

def UndirEdge {VertSet : Type*} (G : SimpGraph VertSet) :
    Set (Sym2 VertSet) := Set.range (VertSet_to_Sym2 G)



-- We need to determine that the set of undirected edges is finite in order to count them.
--Since we know that V is finite, we know that V × V will be finite

-- We us noncomputable as it will need a classical reasoning. We also use 'instance' so that,
-- given a finite vertex type V, we can treat G.DirEdge as a finite type as well
noncomputable
instance (X : FinGraph) : Fintype (DirEdge X.G) := by
    classical
    -- Prove G.DirEdge has finitely many elements
    have : Finite (DirEdge X.G) := by
        -- V × V is finite because V is fintype, can inject G.DirEdge into V × V
        refine Finite.of_injective (fun e : DirEdge X.G => e.1) ?_
        -- Now prove injectiviyt of the function
        intro a b hab
        -- equality of subtypes is determined by equality of underlying values
        apply Subtype.ext
        simpa using hab
    exact Fintype.ofFinite (DirEdge X.G)


-- We now want to prove that the set of undirected edges is finite. We can use that the range
-- of any function from a finite domain must be finite, a lemma given by Set.finite_range
noncomputable
instance (X : FinGraph) : Fintype (↑(UndirEdge X.G)) := by
    classical
    exact Fintype.ofFinite _

-- We now want to prove symmetry, i.e. that if adj u v then adj v u. We us the structure of
-- SimpGraph where we have symm : Symmetric adj to prove this.
lemma adj_swap {VertSet : Type*} (G : SimpGraph VertSet) (u v : VertSet) (h : G.adj u v) :
    G.adj v u := G.symm h
