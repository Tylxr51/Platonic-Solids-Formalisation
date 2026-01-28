import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2
import MA4N1_Platonic_Solids.Simple_Graph_Theory

-- We currently count directed edges as ordered pairs. We now want an undirected edge set.
-- That is, instead of DirEdgeSet = {(u,v) | G.adj u v}, we have EdgeSet = {{u,v} | G.adj uv}
-- So we want to identfy (u,v) and (v,u) to be the same, so I will attempt to create a quotient map.

namespace SimpGraph

variable {V : Type*} (G : SimpGraph V)
-- To define functions around these edges, it might be best to repurpose the definition to suit
-- our needs. This give us a term 'e' consisting of the pair (u,v) (given by e.1) and a proof
-- that adj u v (given by e.2)
def DirEdge (G : SimpGraph V) : Type _ := {e: V × V // G.adj e.1 e.2}
def V_to_Sym2 (G : SimpGraph V) : G.DirEdge → Sym2 V := fun e => Sym2.mk e.1
def UndirEdge (G : SimpGraph V) : Set (Sym2 V) := Set.range (G.V_to_Sym2)

-- We need to determine that the set of undirected edges is finite in order to count them.
--Since we know that V is finite, we know that V × V will be finite

-- We us noncomputable as it will need a classical reasoning. We also use 'instance' so that,
-- given a finite vertex type V, we can treat G.DirEdge as a finite type as well
noncomputable
instance (G : SimpGraph V) [Fintype V] : Fintype (G.DirEdge) := by
  classical
 -- Prove G.DirEdge has finitely many elements
  have : Finite (G.DirEdge) := by
    -- V × V is finite because V is fintype, can inject G.DirEdge into V × V
    refine Finite.of_injective (fun e : G.DirEdge => e.1) ?_
    -- Now prove injectiviyt of the function
    intro a b hab
    -- equality of subtypes is determined by equality of underlying values
    apply Subtype.ext
    simpa using hab
  exact Fintype.ofFinite (G.DirEdge)

-- We now want to prove that the set of undirected edges is finite. We can use that the range
-- of any function from a finite domain must be finite, a lemma given by Set.finite_range
noncomputable
instance [Fintype V] (G : SimpGraph V) : Fintype (↑(G.UndirEdge)) := by
  classical
  exact (Set.finite_range (G.V_to_Sym2)).fintype

-- We now want to prove symmetry, i.e. that if adj u v then adj v u. We us the structure of
-- SimpGraph where we have symm : Symmetric adj to prove this.
lemma adj_swap {u v : V} (h : G.adj u v) : G.adj v u := G.symm h

-- Similarly, we want that if adj u v then u ≠ v, which comes from Irreflexive adj
lemma adj_neq {u v : V} (h : G.adj u v) : u ≠ v := by
  intro huv
  have h1 : G.adj u u := by simpa [huv] using h
  exact G.loopless u h1

-- In Sym2, the pairs (u, v) and (v, u) represent the same element
lemma sym2_comm {u v : V} : Sym2.mk (u, v) = Sym2.mk (v, u) := by
  apply (Sym2.mk_eq_mk_iff (p := (u, v)) (q := (v, u))).2
  right
  rfl

-- It is clear that the only way to represent {u, v} is by either (u, v) or (v, u) and so this is
-- what we want to show next
lemma sym2_classify {u1 v1 u2 v2 : V} (h : Sym2.mk (u1, v1) = Sym2.mk (u2, v2)) :
(u1 = u2 ∧ v1 = v2) ∨ (u1 = v2 ∧ v1 = u2) := by
    have h1 : ((u1, v1) = (u2, v2)) ∨ ((u1, v1) = (u2, v2).swap) := by
      exact (Sym2.mk_eq_mk_iff (p := (u1, v1)) (q := (u2, v2))).1 h

    -- We can now split into two cases, namely (u1, v1) = (u2, v2) & (u1, v1) = (u2, v2).swap
    rcases h1 with h11 | h12
    · left
      cases h11
      exact ⟨rfl, rfl⟩
    · right
      have h2 : (u1, v1) = (v2, u2) := by
        simpa using h12
      cases h2
      exact ⟨rfl, rfl⟩

-- Now we want to approach the undirected version of the handshaking lemma. to do so, we need to
-- define the undirected edge set, define a map from the directed edges (u, v) to undirected
-- edges {u, v}, and show this map is 2-to-1. That is, every {u, v} with adj u v has two distinct
-- direct representatives (u, v) or (v, u). We then use this to conclude that
-- |DirEdge| = 2 * |UndirEdge|.

noncomputable
def UndirEdgeNum [Fintype V] (G : SimpGraph V) [DecidableRel G.adj] : ℕ :=
Finset.card (G.UndirEdge.toFinset)

-- We want that the pre-image of an undirected edge 'a' under the map V_to_Sym2 has size 2 for any
-- choice of undirected edge 'a'. We need to define this pre-image first.
-- Recall that we defined DirEdge to be a pair of data, namely a pair of ordered vertices, and a
-- proof that u and v are adjacent via adj u v.
def pre_image [Fintype V] (G : SimpGraph V) (x : ↑(G.UndirEdge)) : Type _ :=
{e : G.DirEdge // G.V_to_Sym2 e = x}

-- So the pre-image shoul, for h : G.adj u v consist of
  -- ⟨(u, v), h⟩
  -- ⟨(v, u), G.symm h⟩
-- distinct via adj_neq

-- The following definition will take a pair of vertices u v and a proof of adjacency to construct
-- the directed edge (u, v)
def DirEdgeBuild {u v : V} (G : SimpGraph V) (h : G.adj u v) : G.DirEdge := ⟨(u, v), h⟩
-- Now this gives us, given a pair of vertices and an adjacency proof h : G.adj u v, the following:
  -- ⟨(u, v), h⟩ via DirEdgeBuild G h
  -- ⟨(v, u), via DirEdgeBuild G (G.symm h)
-- We will rename these so that they are more intuitive to work with
def e1 {u v : V} (G : SimpGraph V) (h : G.adj u v) : G.DirEdge := DirEdgeBuild G h
def e2 {u v : V} (G : SimpGraph V) (h : G.adj u v) : G.DirEdge := DirEdgeBuild G (G.symm h)

-- Our aim now is to prove that {u, v} has exactly the two elements e1 and e2 stated above. We can
-- characterise {u, v} by its members (u, v) & (v, u)
lemma characterise_members (G : SimpGraph V) {u v : V} (h : G.adj u v) (e : G.DirEdge) :
G.V_to_Sym2 e = Sym2.mk (u, v) ↔ e.1 = (u, v) ∨ e.1 = (v, u) := by
constructor -- Break into the forward and backward directions
· intro heq1
  have ha : (e.1.1 = u ∧ e.1.2 = v) ∨ (e.1.1 = v ∧ e.1.2 = u)
  have : Sym2.mk e.1 = Sym2.mk (u, v) := by
    simpa [V_to_Sym2] using heq1
  exact (sym2_classify (u1 := e.1.1) (v1 := e.1.2) (u2 := u) (v2 := v) this)

  cases ha with
  | inl huv =>
    left
    rcases huv with ⟨hu, hv⟩
    ext <;> simp [hu, hv]
  | inr hvu =>
     right
     rcases hvu with ⟨hu, hv⟩
     ext <;> simp [hu, hv]
· intro heq2
  cases heq2 with
  | inl hpair =>
      simp [V_to_Sym2, hpair]
  | inr hpair =>
  sorry
sorry


end SimpGraph
