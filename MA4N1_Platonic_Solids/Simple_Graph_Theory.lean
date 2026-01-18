import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2

-- In this file, we define simple graphs and some of their related definitions
-- such as vertex neighbourhoods and directed edge sets.
-- Our definition of directed edge sets differs from the traditional definition
-- as we have ordered pairs of vertices rather than unordered.
-- This means that our version of the hanshaking lemma is that the sum of the
-- degrees is equal to size of the directed edge set.
-- Using Sym2 it shouldn't be too difficult to give a defintion for the
-- usual edgeset and show that the cardinality of this is half the cardinality
-- of the directed edge set, thus proving the traditional form of the
-- handshaking lemma


-- We define a graph as a vertex type V with an adjacency relation adj
-- This is the same as the definition in mathlib, however from this point
-- I didn't look at any of SimpleGraph in mathlib, so any similarities are
-- purely coincidental
structure SimpGraph (V : Type*) where
(adj : V → V → Prop)
(symm : Symmetric adj)
(loopless : Irreflexive adj)

-- I made this definition just as a test, it is not used again.
def FinSimpGraph.Size
  {V : Type*} [Fintype V] (G : SimpGraph V) [∀ v w, Decidable (G.adj v w)] : ℕ :=
  Fintype.card V

-- Standard definition of the neighbourhood of a vertex
def SimpGraph.Nbhd {V : Type*} (G : SimpGraph V) (v : V) : Set V :=
  {u | G.adj v u}

-- The adjacent edgeset of a vertex v is the set of directed edges from v.
-- As with many of the following definitions, this should technically be
-- unordered pairs but in this case it doesn't make much difference for us
def SimpGraph.AdjEdgeset {V : Type*} (G : SimpGraph V) (v : V) : Set (V × V) :=
  {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v}

-- Needed to show that if V is finite then so is any adjacent edgeset
noncomputable
instance SimpGraph.FinAdjEdgeset {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) :
  Fintype ↑(G.AdjEdgeset v) := by
  have h1 : (G.AdjEdgeset v).Finite := by
      rw[AdjEdgeset]
      simp
      rw[Nbhd]
      simp
      exact Set.finite_univ.subset (by intro x hx; trivial)
  exact h1.fintype

-- I needed to be able to convert the adjacent edgeset to a finset for our
-- argument in the case that V is finite. That is what this defintion does
noncomputable
def SimpGraph.AdjEdgeFinset {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) :
  Finset (V×V) :=
  (G.AdjEdgeset v).toFinset

-- Typically, the degree might be defined as the cardinality of the neighbourhood
-- but it is easy to see that this definition is equivalent.
-- It would also be possible to generalise this definition to locally finite
-- graphs, but that was beyond the scope of the project.
noncomputable
def FinSimpGraph.Deg {V : Type*} [Fintype V] (G : SimpGraph V) (v : V) : ℕ   :=
 Finset.card (SimpGraph.AdjEdgeFinset G v)

-- Degsum is the sum of the degrees #wow
noncomputable
def FinSimpGraph.Degsum {V : Type*} [Fintype V] (G : SimpGraph V) : ℕ   :=
 ∑ v : V, (FinSimpGraph.Deg G v)

-- Defining the directed edgeset of a graph. Again, since we are working with
-- simple graphs this should really be unordered pairs.
-- Should be able to correct this with Sym2 but I was too far in by the time
-- I noticed
def SimpGraph.DirEdgeset {V : Type*} (G : SimpGraph V)
 : Set (V×V) :=
{ (u,v) | G.adj u v }

-- Our first lemma, showing that the union of all the adjacent edgesets of
-- each vertex is the edgeset of the graph #noway
lemma SimpGraph.EdgesetEqUnionAdjEdge {V : Type*} (G : SimpGraph V) :
(⋃ v, SimpGraph.AdjEdgeset G v) = SimpGraph.DirEdgeset G :=  by
  ext
  apply Iff.intro
  · simp
    intro x
    rw[AdjEdgeset]
    rw[Nbhd]
    rw[DirEdgeset]
    simp
    intro h1 h2
    rw[h1]
    exact h2

  simp
  rw[DirEdgeset]
  intro h1
  rename_i x
  have h3 : x ∈ G.AdjEdgeset x.1 := by
    rw[AdjEdgeset]
    simp
    rw[Nbhd]
    simp
    apply h1
  apply Exists.intro _
  apply h3

-- Similar to what we did for AdjEdgeset, we need that if the graph is finite
-- then so is the edgeset
noncomputable
instance SimpGraph.FinEdgeset {V : Type*} [Fintype V] (G : SimpGraph V) :
  Fintype ↑(G.DirEdgeset) := by
  have h1 : (G.DirEdgeset).Finite := by
      rw[DirEdgeset]
      simp
      exact Set.finite_univ.subset (by intro x hx; trivial)
  exact h1.fintype

-- and need a definition to convert the edgeset to a finset in this case
noncomputable
def SimpGraph.DirNoEdges {V : Type*} [Fintype V] (G : SimpGraph V) : ℕ :=
Finset.card (SimpGraph.DirEdgeset G).toFinset

-- In order to say that the cardinality of the union of the adjedgesets
-- is the sum of the cardinalities, we need this lemma that the adjedgesets
-- are disjoint
lemma SimpGraph.DirEdgesetDisjoint {V : Type*} (G : SimpGraph V) :
∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeset v) (G.AdjEdgeset u) := by
  intro u v hneq
  rw[Disjoint]
  simp
  intro x h1 h2
  ext
  simp
  by_contra
  rename_i y h4
  have h5 : y ∈ {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v} := by
    apply h2
    exact h4
  have hy : y.1 = v ∧ y.2 ∈ G.Nbhd v := by
    simpa
  have h6 : y.1 = v := by
    exact hy.1

  have h7 : y ∈ {(v',w) : V × V | v'=u ∧ w ∈ SimpGraph.Nbhd G u} := by
    apply h1
    exact h4
  have hy' : y.1 = u ∧ y.2 ∈ G.Nbhd u := by
    simpa
  have h8 : y.1 = u := by
    exact hy'.1
  have h9 : u=v := by
    exact h8.symm.trans h6
  contradiction

-- I then realised that I actually need this for the finite case and lean
-- is too thick to easily go between the two. This could probably be proven
-- fairly quickly from the previous lemma, but I just copy and pasted that
-- proof and then edited it to make it work
lemma SimpGraph.DirEdgeFinsetDisjoint {V : Type*} [Fintype V] (G : SimpGraph V) :
∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeFinset v) (G.AdjEdgeFinset u) := by
  intro u v hneq
  rw[Disjoint]
  simp
  rw[AdjEdgeFinset]
  rw[AdjEdgeFinset]
  simp
  intro x h1 h2
  ext
  simp
  by_contra
  rename_i y h4
  have h5 : y ∈ {(v',u) : V × V | v'=v ∧ u ∈ SimpGraph.Nbhd G v} := by
    apply h2
    exact h4
  have hy : y.1 = v ∧ y.2 ∈ G.Nbhd v := by
    simpa
  have h6 : y.1 = v := by
    exact hy.1

  have h7 : y ∈ {(v',w) : V × V | v'=u ∧ w ∈ SimpGraph.Nbhd G u} := by
    apply h1
    exact h4
  have hy' : y.1 = u ∧ y.2 ∈ G.Nbhd u := by
    simpa
  have h8 : y.1 = u := by
    exact hy'.1
  have h9 : u=v := by
    exact h8.symm.trans h6
  contradiction

-- Finally, here is our directed version of the handshaking lemma
theorem SimpGraph.DirHandshake {V : Type*} [Fintype V] (G : SimpGraph V)
: SimpGraph.DirNoEdges G = FinSimpGraph.Degsum G := by
  classical
  rw[DirNoEdges]
  rw[FinSimpGraph.Degsum]
  simp [FinSimpGraph.Deg]
  have hdis : ∀ ⦃v u : V⦄, v ≠ u → Disjoint (G.AdjEdgeFinset v) (G.AdjEdgeFinset u) := by
    exact SimpGraph.DirEdgeFinsetDisjoint G
  have hpdis :
  (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint G.AdjEdgeFinset := by
    intro u hu v hv hne
    exact hdis hne
  have hsumunion  : Finset.card (Finset.biUnion Finset.univ (G.AdjEdgeFinset))
  = ∑ x, Finset.card (G.AdjEdgeFinset x)  := by
    simpa using
      (Finset.card_biUnion
        (s := (Finset.univ : Finset V))
        (t := G.AdjEdgeFinset)
        (hpdis))
  rw[← hsumunion]
  have hunioneq : Finset.univ.biUnion G.AdjEdgeFinset = G.DirEdgeset.toFinset := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
    simp [AdjEdgeFinset]
    simp [← SimpGraph.EdgesetEqUnionAdjEdge]
  simp [hunioneq]


-- Here is my first attempt at proving the lemma using induction.
-- I only managed the base case and I have since changed a few definitions
-- so it probably won't run anymore, but I spent so long on it that I want
-- it to be in here somewhere haha

-- theorem FinSimpGraph.Handshake {V : Type*} [Fintype V] (G : SimpGraph V)
-- [∀ v, DecidablePred (FinSimpGraph.Nbhd G v)] [DecidablePred G.DirEdgeset]
-- :  FinSimpGraph.Degsum (G) = SimpGraph.NoEdges G := by
--    classical
--    rw[SimpGraph.NoEdges]
--    generalize hE : (Finset.filter G.DirEdgeset Finset.univ) = E
--    revert hE
--    refine Finset.induction_on (E) ?base ?step
--    intro hE
--    simp
--    rw[Degsum]
--    rw [Finset.sum_eq_zero_iff]
--   simp
--    intro i
--    rw[Deg]
--    rw[Finset.card_eq_zero]
--   simp
--    rw[FinSimpGraph.Nbhd]
--    intro x
--    change ¬ G.adj i x
--    by_contra adj
--    have nempty : (i,x) ∈ Finset.filter G.DirEdgeset Finset.univ := by
--      simp
--      rw[SimpGraph.DirEdgeset]
--      change (G.adj i x)
--      exact adj
--
--    have isempty : (i,x) ∉ Finset.filter G.DirEdgeset Finset.univ := by
--        simp [hE]
--
--    contradiction
--
--    simp
  --induction SimpGraph.NoEdges G with
  --| zero =>
  --rw [mul_zero]
  --rw [Degsum]
  --rw [Finset.sum_eq_zero_iff]
  --simp
  --intro i
  --rw[Deg]
  --rw[Finset.card_eq_zero]
  --simp
  --intro x
  --rw[FinSimpGraphNbhd]
