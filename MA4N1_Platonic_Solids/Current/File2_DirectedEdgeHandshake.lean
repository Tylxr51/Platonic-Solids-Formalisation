import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
-- Defining the directed edgeset of a graph. Again, since we are working with
-- simple graphs this should really be unordered pairs.
-- Should be able to correct this with Sym2 but I was too far in by the time
-- I noticed
def SimpGraph.DirEdgeset {V : Type*} (G : SimpGraph V) :
    Set (V × V) :=
    { (u,v) | G.adj u v }

-- Our first lemma, showing that the union of all the adjacent edgesets of
-- each vertex is the edgeset of the graph #noway
lemma SimpGraph.EdgesetEqUnionAdjEdge {V : Type*} (G : SimpGraph V) :
(⋃ v, SimpGraph.AdjEdgeset G v) = SimpGraph.DirEdgeset G :=  by
    ext
    apply Iff.intro
    ·   simp
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
instance FinGraph.FinEdgeset (X : FinGraph) :
    Fintype ↑(X.G.DirEdgeset) := by
    have h1 : (X.G.DirEdgeset).Finite := by
        unfold SimpGraph.DirEdgeset
        simp
        exact Set.finite_univ.subset (by intro x hx; trivial)
    exact h1.fintype

-- and need a definition to convert the edgeset to a finset in this case
noncomputable
def FinGraph.DirNoEdges (X : FinGraph) : ℕ :=
    Finset.card (SimpGraph.DirEdgeset X.G).toFinset

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
lemma FinGraph.DirEdgeFinsetDisjoint (X : FinGraph) :
∀ ⦃v u : X.VertSet⦄, v ≠ u → Disjoint (X.AdjEdgeFinset v) (X.AdjEdgeFinset u) := by
    intro u v hneq
    rw[Disjoint]
    simp
    unfold FinGraph.AdjEdgeFinset
    simp
    intro x h1 h2
    ext
    simp
    by_contra
    rename_i y h4
    have h5 : y ∈ {(v',u) : (X.VertSet × X.VertSet) | v'=v ∧ u ∈ SimpGraph.Nbhd X.G v} := by
        apply h2
        exact h4
    have hy : y.1 = v ∧ y.2 ∈ X.G.Nbhd v := by
        simpa
    have h6 : y.1 = v := by
        exact hy.1

    have h7 : y ∈ {(v',w) : (X.VertSet × X.VertSet) | v'=u ∧ w ∈ SimpGraph.Nbhd X.G u} := by
        apply h1
        exact h4
    have hy' : y.1 = u ∧ y.2 ∈ X.G.Nbhd u := by
        simpa
    have h8 : y.1 = u := by
        exact hy'.1
    have h9 : u=v := by
        exact h8.symm.trans h6
    contradiction

-- Finally, here is our directed version of the handshaking lemma
theorem FinGraph.DirHandshake (X : FinGraph) : FinGraph.DirNoEdges X = FinGraph.Degsum X := by
  classical
  rw[DirNoEdges]
  rw[FinGraph.Degsum]
  simp [FinGraph.Deg]
  have hdis : ∀ ⦃v u : X.VertSet⦄, v ≠ u → Disjoint (X.AdjEdgeFinset v) (X.AdjEdgeFinset u) := by
    exact FinGraph.DirEdgeFinsetDisjoint X
  have hpdis :
  (↑(Finset.univ : Finset X.VertSet) : Set X.VertSet).PairwiseDisjoint X.AdjEdgeFinset := by
    intro u hu v hv hne
    exact hdis hne
  have hsumunion  : Finset.card (Finset.biUnion Finset.univ (X.AdjEdgeFinset))
  = ∑ x, Finset.card (X.AdjEdgeFinset x)  := by
    simpa using
      (Finset.card_biUnion
        (s := (Finset.univ : Finset X.VertSet))
        (t := X.AdjEdgeFinset)
        (hpdis))
  rw[← hsumunion]
  have hunioneq : Finset.univ.biUnion X.AdjEdgeFinset = X.G.DirEdgeset.toFinset := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
    simp [AdjEdgeFinset]
    simp [← SimpGraph.EdgesetEqUnionAdjEdge]
  simp [hunioneq]
