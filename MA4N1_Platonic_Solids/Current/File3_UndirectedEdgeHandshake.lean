import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
import MA4N1_Platonic_Solids.Current.File2_DirectedEdgeHandshake

import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring


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
-- Since we know that X.VertSet is finite, we know that X.VertSet × X.VertSet will be finite

-- We use noncomputable as it will need a classical reasoning. We also use 'instance' so that,
-- given a finite vertex type VertSet, we can treat DirEdge X.G as a finite type as well
noncomputable
instance (X : FinGraph) : Fintype (DirEdge X.G) := by
    classical
    -- Prove DirEdge X.G has finitely many elements
    have : Finite (DirEdge X.G) := by
        -- X.VertSet × X.VertSet is finite because X.VertSet is fintype, can inject DirEdge X.G
        -- into X.VertSet × X.VertSet
        refine Finite.of_injective (fun e : DirEdge X.G => e.1) ?_
        -- Now prove injectivity of the function
        intro a b hab
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


-- Similarly, we want that if adj u v then u ≠ v, which comes from Irreflexive adj
lemma adj_neq {VertSet : Type*} (G : SimpGraph VertSet) (u v : VertSet) (h : G.adj u v) :
    u ≠ v := by
        intro huv
        have h1 : G.adj u u := by simpa [huv] using h
        exact G.loopless u h1


-- In Sym2, the pairs (u, v) and (v, u) represent the same element
lemma sym2_comm {VertSet : Type*} (u v : VertSet) :
    Sym2.mk (u, v) = Sym2.mk (v, u) := by
        apply (Sym2.mk_eq_mk_iff (p := (u, v)) (q := (v, u))).2
        right
        rfl


-- It is clear that the only way to represent {u, v} is by either (u, v) or (v, u) and so this is
-- what we want to show next
lemma sym2_classify {VertSet : Type*} (u1 v1 u2 v2 : VertSet)
    (h : Sym2.mk (u1, v1) = Sym2.mk (u2, v2)) :
(u1 = u2 ∧ v1 = v2) ∨ (u1 = v2 ∧ v1 = u2) := by
    have h1 : ((u1, v1) = (u2, v2)) ∨ ((u1, v1) = (u2, v2).swap) := by
        exact (Sym2.mk_eq_mk_iff (p := (u1, v1)) (q := (u2, v2))).1 h

    -- We can now split into two cases, namely (u1, v1) = (u2, v2) & (u1, v1) = (u2, v2).swap
    rcases h1 with h11 | h12
    ·   left
        cases h11
        exact ⟨rfl, rfl⟩
    ·   right
        have h2 : (u1, v1) = (v2, u2) := by
            simpa using h12
        cases h2
        exact ⟨rfl, rfl⟩


-- Now we want to approach the undirected version of the handshaking lemma. To do so, we need to
-- define the undirected edge set, define a map from the directed edges (u, v) to undirected
-- edges {u, v}, and show this map is 2-to-1. That is, every {u, v} with adj u v has two distinct
-- direct representatives (u, v) or (v, u). We then use this to conclude that
-- |DirEdge| = 2 * |UndirEdge|.
noncomputable
def UndirEdgeNum (X : FinGraph) [DecidableRel X.G.adj] : ℕ :=
    Finset.card ((UndirEdge X.G).toFinset)


-- We want that the pre-image of an undirected edge 'ue' under the map VertSet_to_Sym2 has size 2
-- for any choice of undirected edge 'ue'. We need to define this pre-image first.
def pre_image (X : FinGraph) (ue : ↑(UndirEdge X.G)) :
    Type _ := {e : DirEdge X.G // VertSet_to_Sym2 X.G e = ue}

-- So the pre-image should, for h : X.G.adj u v, consist of
    -- ⟨(u, v), h⟩
    -- ⟨(v, u), X.G.symm h⟩
-- distinct via adj_neq
-- So the next thing to do is to prove that pre_image is finite.

noncomputable
instance (X : FinGraph) (ue : ↑(UndirEdge X.G)) : Fintype (pre_image X ue) := by
    classical
    -- As we previously did, probably easier to show finiteness by injecting into DirEdge X.G
    have : Finite (pre_image X ue) := by
        refine Finite.of_injective (fun y : pre_image X ue => y.1) ?_
        intro a b hab
        apply Subtype.ext
        simpa using hab
    exact Fintype.ofFinite (pre_image X ue)

-- The following definition will take a pair of vertices u v and a proof of adjacency to construct
-- the directed edge (u, v)
def DirEdgeBuild (X : FinGraph) (u v : X.VertSet) (h : X.G.adj u v) : DirEdge X.G := ⟨(u, v), h⟩
-- Now this gives us, given a pair of vertices and an adjacency proof h : X.G.adj u v, the
-- following:
    -- ⟨(u, v), h⟩ via DirEdgeBuild X u v h
    -- ⟨(v, u) G.symm h⟩, via DirEdgeBuild X u v (X.G.symm h)

-- Our aim now is to prove that {u, v} has exactly the two elements. We can characterise {u, v} by
-- its members (u, v) & (v, u)
lemma characterise_members (X : FinGraph) (u v : X.VertSet) (de : DirEdge X.G) :
    VertSet_to_Sym2 X.G de = Sym2.mk (u, v) ↔ de.1 = (u, v) ∨ de.1 = (v, u) := by
        constructor
        ·   intro heq1
            have ha : (de.1.1 = u ∧ de.1.2 = v) ∨ (de.1.1 = v ∧ de.1.2 = u) := by
                have : Sym2.mk de.1 = Sym2.mk (u, v) := by
                    simpa [VertSet_to_Sym2] using heq1
                exact (sym2_classify (u1 := de.1.1) (v1 := de.1.2) (u2 := u) (v2 := v) this)

        -- We have two separate cases to consider, (↑e).1 = u ∧ (↑e).2 = v,
        -- and (↑e).1 = v ∧ (↑e).2 = u
        -- So can split into the left and right hand sides of 'or' (i.e ∨)
            cases ha with
            | inl huv =>
                left
                -- Again, split into two cases of either side of 'and' (i.e ∧)
                rcases huv with ⟨hu, hv⟩
                ext <;> simp [hu, hv]
            | inr hvu =>
                right
                rcases hvu with ⟨hu, hv⟩
                ext <;> simp [hu, hv]
        intro heq2
        cases heq2 with
        | inl hpairl =>
            rw [VertSet_to_Sym2, hpairl]
        | inr hpairr =>
            rw [VertSet_to_Sym2, hpairr]
            exact (sym2_comm (u := u) (v := v)).symm


-- While this lemma says that any directed edge that maps to {u, v} must have the pair (u, v) or
-- (v, u), we need actaully show they exist as directed edges in DirEdge X.G, and then show that
-- they are distinct. Thus we can then conclude that the cardinality of the pre-image is 2, i.e that
-- there are exactly 2 directed edges associated to an undirected edge.

-- To begin with this, we need to pick a representative edge . Since we have
-- 'ue : ↑(UndirEdge X.G)', then we have some ue.1 in the range of VertSet_to_Sym2 X.G, so there
-- exists an edge e with VertSet_to_Sym2 X.G e = ue.1


noncomputable
def chooseDirEdge (X : FinGraph) (ue : ↑(UndirEdge X.G)) : DirEdge X.G := by
    classical
    have h1 : ue.1 ∈ UndirEdge X.G := ue.property
    -- Recall UndirEdge = Set.range (VertSet_to_Sym2)
    dsimp [UndirEdge] at h1
    have h2 : ∃ e : DirEdge X.G, VertSet_to_Sym2 X.G e = ue.1 :=
            (Set.mem_range).1 h1
    exact Classical.choose h2

-- The above definition says that, given an undirected edge ue, pick an edge e that maps to it
-- The following lemma then confirms that the directed edge chosen by the above definition really
-- does map back to ue.

lemma chooseDirEdge_maps_back (X : FinGraph) (ue : ↑(UndirEdge X.G)) :
VertSet_to_Sym2 X.G (chooseDirEdge X ue) = ue.1 := by
    classical
    have h1 : ue.1 ∈ UndirEdge X.G := ue.property
    dsimp [UndirEdge] at h1
    have h2 : ∃ de : DirEdge X.G, VertSet_to_Sym2 X.G de = ue.1 :=
        (Set.mem_range).1 h1
    exact Classical.choose_spec h2


-- We will now prove that the cardinality of 'pre_image ue' is 2
lemma pre_image_card_eq_2 (X : FinGraph) (ue : ↑(UndirEdge X.G)) :
Fintype.card (pre_image X ue) = 2 := by
-- Need classical as we work on the assumption ue is in the range of VertSet_to_Sym2
    classical
    set de : DirEdge X.G := chooseDirEdge X ue with he_def
    have h : VertSet_to_Sym2 X.G de = ue.1 := by
        simpa [he_def] using (chooseDirEdge_maps_back X ue)
    -- Unpack the deifnition of e into its vertex pair and adjacency proof
    rcases de with ⟨⟨u, v⟩, huv⟩
    have hx : Sym2.mk (u, v) = ue.1 := by
        simpa [VertSet_to_Sym2] using h

  -- Define the elements 'a' and 'b' of the pre-image
    let a : pre_image X ue :=
        ⟨⟨(u, v), huv⟩, by
        simpa [VertSet_to_Sym2] using hx⟩

    let b : pre_image X ue :=
        ⟨⟨(v, u), X.G.symm huv⟩, by
        have : Sym2.mk (v, u) = ue.1 := by
            calc
            Sym2.mk (v, u) = Sym2.mk (u, v) := by
                exact (sym2_comm u v).symm
            _ = ue.1 := hx
        simpa [VertSet_to_Sym2] using this⟩

  -- Can now use loopless to show that a and b are distinct.
    have hneq : a ≠ b := by
        intro heq
        have hdir : (a.1 : DirEdge X.G) = b.1 := by
            simpa using congrArg Subtype.val heq
        have hpair : (a.1.1 : X.VertSet × X.VertSet) = b.1.1 := by
            simpa using congrArg Subtype.val hdir
        have huv_eq : u = v := by
            exact congrArg Prod.fst hpair
        exact (adj_neq X.G u v huv) huv_eq

  -- We show now that every element of the pre-image is either 'a' or 'b', thus there are at
  -- most 2 elements of the pre-image
    have cover : ∀ y: pre_image X ue, y = a ∨ y = b := by
        intro y
        -- Rewriting in terms of 'u' and 'v' allows me to use the characterisation lemma I proved
        -- earlier, that any directed edge mapping to the unordered pair {u, v} is either (u, v) or
        -- (v, u)
        have hy0 : VertSet_to_Sym2 X.G y.1 = Sym2.mk (u, v) := by
            simpa [hx.symm] using y.2
        have hy : y.1.1 = (u, v) ∨ y.1.1 = (v, u) := by
            exact (characterise_members X u v (de := y.1)).1 hy0

        -- Now convert this back to pre-image elements as an equality
        cases hy with
        | inl hp =>
            left
            apply Subtype.ext
            apply Subtype.ext
            simpa [a] using hp
        | inr hp =>
            right
            apply Subtype.ext
            apply Subtype.ext
            simpa [b] using hp

  -- To conclude that the pre-image has size 2, we construct an equivalence with Fin 2, the
  -- standard type of size 2. We construct a map forwards & backwards, and then show that the
  -- composition of them is the iddntity on each side.
    classical
    let e2 : (pre_image X ue) ≃ Fin 2 :=
    { -- First, map a ↦ 0, b ↦ 1
        toFun := fun y =>
        if hya : y = a then (0 : Fin 2) else (1 : Fin 2)
        -- Then the inverse map, 0 ↦ a, 1 ↦ b
        invFun := fun i =>
        if hi0 : i = (0 : Fin 2) then a else b
        -- invFun ∘ toFun = id
        left_inv := by
            intro y
            rcases cover y with hya | hyb
            ·   subst hya
                simp
            ·   subst hyb
                -- toFun b = 1 (since b ≠ a), invFun 1 = b
                have hba : (b : pre_image X ue) ≠ a := by
                    intro h
                    exact hneq (h.symm)
                simp [hba]
        -- toFun ∘ invFun = id
        right_inv := by
            intro i
            -- Fin 2 has only 0 or 1, so can split into cases i = 0 or i = 1
            by_cases hi0 : i = (0 : Fin 2)
            ·   subst hi0
                simp
            ·   have hi1 : i = (1 : Fin 2) := by
                    fin_cases i <;> simp at hi0 ⊢
                subst hi1
                -- show toFun b = 1
                have hbneqa : (b : pre_image X ue) ≠ a := by
                    intro h
                    exact hneq (h.symm)
                simp [hbneqa, hi0] }

  -- Equivalent finite types have the same cardinality, using card (Fin 2) = 2
    have hcard2 : Fintype.card (pre_image X ue) = Fintype.card (Fin 2) :=
        Fintype.card_congr e2
    simpa using hcard2


-- Now we are done with this, we need to relate it back to the original handshake lemma
-- and conclude the new result. This requires linking the new and old definitions via maps

-- The following definition will map a directed edge to its correpsonding undirected edge
noncomputable
def to_Undir (X : FinGraph) (de : DirEdge X.G) :
    ↑(UndirEdge X.G) := ⟨VertSet_to_Sym2 X.G de, ⟨de, rfl⟩⟩


-- Before proceeding any further, it is important to make the following equivalence:
noncomputable
def pre_image_equiv (X : FinGraph) (ue : ↑(UndirEdge X.G)) :
    pre_image X ue ≃ {de : DirEdge X.G // to_Undir X de = ue} := by
-- We have the functions VertSet_to_Sym2 : DirEdge → Sym2 VertSet, and
-- to_Undir : DirEdge → UndirEdge
-- So while VertSet_to_Sym2 maps directly into Sym2 VertSet, to_Undir instead takes the result as an
-- element of the subtype UndirEdge = Set.range VertSet_to_Sym2. This equivalence identifies that
-- the objects are mathematically the same, the directed edge mapping to a given undirected edge.
    refine
    {   toFun := fun y => ⟨y.1, ?_⟩
        invFun := fun y => ⟨y.1, ?_⟩
        left_inv := by
            intro y ; rfl
        right_inv := by
            intro y; rfl }
    ·   apply Subtype.ext
        simpa [to_Undir] using y.2
    ·   have : (to_Undir X y.1 : Sym2 X.VertSet) = (ue : Sym2 X.VertSet) := congrArg Subtype.val y.2
        simpa [to_Undir] using this


-- We now introduce the lemma that the number of directed edges is twice the number of
-- undirected edges
theorem card_DirEdge_eq_two_card_UndirEdge (X : FinGraph) :
    Fintype.card (DirEdge X.G) = 2 * Fintype.card (↑(UndirEdge X.G)) := by
  classical
  let f : DirEdge X.G → ↑(UndirEdge X.G) := to_Undir X

  calc
    Fintype.card (DirEdge X.G)
        = Fintype.card (Σ ue : ↑(UndirEdge X.G), {de : DirEdge X.G // f de = ue}) := by
          -- domain ≃ disjoint union of fibers
          simpa using (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ ue : ↑(UndirEdge X.G), Fintype.card {de : DirEdge X.G // f de = ue} := by
          -- card of sigma = sum of cards
          simp
    _ = ∑ ue : ↑(UndirEdge X.G), Fintype.card (pre_image X ue) := by
          -- replace fibers with your `pre_image` via the equivalence
          refine Finset.sum_congr rfl ?_
          intro ue _
          simpa [f] using (Fintype.card_congr (pre_image_equiv X (ue := ue))).symm
    _ = ∑ _ue : ↑(UndirEdge X.G), 2 := by
          -- each preimage has card 2
          refine Finset.sum_congr rfl ?_
          intro ue _
          simpa using (pre_image_card_eq_2 X (ue := ue))
    _ = 2 * Fintype.card (↑(UndirEdge X.G)) := by
          -- sum of constant = constant * number of terms
          simp [Finset.card_univ]
          ring


-- We have almost everything we need now, but we first need to connect what is in this file to
-- File2_DirectedEdgeHandshake file. To do this, we need to show that 'DirNoEdges = |DirEdges|',
-- bridging the two deifnitions, and then that 'UndirEdgeNum = |UndirEdge|'

noncomputable
def DirEdge_equiv_DirEdgeset (X : FinGraph) : DirEdge X.G ≃ ↑(SimpGraph.DirEdgeset X.G) :=  by
    classical
    refine
    {   toFun := fun e => ⟨e.1, ?_⟩
        invFun := fun e => ⟨e.1, ?_⟩
        left_inv := by
            intro e ; rfl
        right_inv := by
            intro e ; rfl }
    ·   simp
    ·   aesop

lemma DirNoEdges_eq_card_DirEdge (X : FinGraph) [DecidableRel X.G.adj] :
    FinGraph.DirNoEdges X = Fintype.card (DirEdge X.G) := by
    classical
    -- We first convert DirNoEdges into the cardinality of the subtype ↑(DirEdgeset X.G)
    have h1 : FinGraph.DirNoEdges X = Fintype.card (↑(SimpGraph.DirEdgeset X.G)) := by
        simp [FinGraph.DirNoEdges]
    have h2 : Fintype.card (↑(SimpGraph.DirEdgeset X.G)) = Fintype.card (DirEdge X.G) := by
        simpa using (Fintype.card_congr (DirEdge_equiv_DirEdgeset X))
    exact h1.trans h2


-- We now have the undirected version of the statement, that UndirEdgeNum is the cardinality of the
--  subtype ↑(UndirEdge X.G)
lemma UndirEdgeNum_eq_card_UndirEdge (X : FinGraph) [DecidableRel X.G.adj] :
    UndirEdgeNum X = Fintype.card (↑(UndirEdge X.G)) := by
        classical
        simp [UndirEdgeNum]


-- We can finally put this all together and conclude the reuslt of the handshake lemma for
-- undirected graphs. We will rewrite some of the results as hypotheses that we can insert here.
theorem UndirHandshake (X : FinGraph) [DecidableRel X.G.adj] :
    FinGraph.Degsum X = 2 * UndirEdgeNum X := by

        have hdirhand : FinGraph.DirNoEdges X = FinGraph.Degsum X :=
            FinGraph.DirHandshake X
        have hdircard : FinGraph.DirNoEdges X = Fintype.card (DirEdge X.G) :=
            DirNoEdges_eq_card_DirEdge X
        have htwo : Fintype.card (DirEdge X.G) = 2 * Fintype.card (↑(UndirEdge X.G)) :=
        card_DirEdge_eq_two_card_UndirEdge X
        have hundir : UndirEdgeNum X = Fintype.card (↑(UndirEdge X.G)) :=
            UndirEdgeNum_eq_card_UndirEdge X

        calc
            FinGraph.Degsum X = FinGraph.DirNoEdges X := by
                simp [hdirhand]
            _ = Fintype.card (DirEdge X.G) := hdircard
            _ = 2 * Fintype.card (↑(UndirEdge X.G)) := htwo
            _ = 2 * UndirEdgeNum X := by
                simp [hundir]
