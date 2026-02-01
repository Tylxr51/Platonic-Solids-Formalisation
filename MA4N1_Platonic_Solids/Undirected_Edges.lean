import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2
import MA4N1_Platonic_Solids.Simple_Graph_Theory

-- We currently count directed edges as ordered pairs. We now want an undirected edge set.
-- That is, instead of DirEdgeSet = {(u,v) | G.adj u v}, we have EdgeSet = {{u,v} | G.adj uv}
-- So we want to identfy (u,v) and (v,u) to be the same, so I will attempt to create a quotient map.

namespace SimpGraph
-- Retrieve the variables used in Simple_Graph_Theory.lean
variable {V : Type*} (G : SimpGraph V)
-- To define functions around these edges, it might be best to repurpose the definition to suit
-- our needs. This give us a term (edge) 'e' consisting of the pair (u,v) (given by e.1) and a proof
-- that adj u v (given by e.2)
def DirEdge : Type _ := {e: V × V // G.adj e.1 e.2}
-- Though conceptually the same as DirEdgeset, I expect this to be easier for working with functions
-- especially considering it encodes a pair (a vertices pair and their proof of adjacency)
def V_to_Sym2 : G.DirEdge → Sym2 V := fun e => Sym2.mk e.1
def UndirEdge : Set (Sym2 V) := Set.range (G.V_to_Sym2)

-- We need to determine that the set of undirected edges is finite in order to count them.
--Since we know that V is finite, we know that V × V will be finite

-- We us noncomputable as it will need a classical reasoning. We also use 'instance' so that,
-- given a finite vertex type V, we can treat G.DirEdge as a finite type as well
noncomputable
instance [Fintype V] : Fintype (G.DirEdge) := by
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
instance [Fintype V] : Fintype (↑(G.UndirEdge)) := by
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
def UndirEdgeNum [Fintype V] [DecidableRel G.adj] : ℕ :=
Finset.card (G.UndirEdge.toFinset)

-- We want that the pre-image of an undirected edge 'a' under the map V_to_Sym2 has size 2 for any
-- choice of undirected edge 'a'. We need to define this pre-image first.
-- Recall that we defined DirEdge to be a pair of data, namely a pair of ordered vertices, and a
-- proof that u and v are adjacent via adj u v.
def pre_image [Fintype V] (x : ↑(G.UndirEdge)) : Type _ :=
{e : G.DirEdge // G.V_to_Sym2 e = x}

-- So the pre-image should, for h : G.adj u v, consist of
  -- ⟨(u, v), h⟩
  -- ⟨(v, u), G.symm h⟩
-- distinct via adj_neq
-- So the enxt thing to do is to prove that pre_image is finite.

noncomputable
instance [Fintype V] (x : ↑(G.UndirEdge)) : Fintype (G.pre_image x) := by
  classical
  -- As we previously did, probably easier to show finiteness by injecting into G.DirEdge
  have : Finite (G.pre_image x) := by
    refine Finite.of_injective (fun y : G.pre_image x => y.1) ?_
    intro a b hab
    apply Subtype.ext
    simpa using hab
  exact Fintype.ofFinite (G.pre_image x)

-- The following definition will take a pair of vertices u v and a proof of adjacency to construct
-- the directed edge (u, v)
def DirEdgeBuild {u v : V} (h : G.adj u v) : G.DirEdge := ⟨(u, v), h⟩
-- Now this gives us, given a pair of vertices and an adjacency proof h : G.adj u v, the following:
  -- ⟨(u, v), h⟩ via DirEdgeBuild G h
  -- ⟨(v, u) G.symm h⟩, via DirEdgeBuild G (G.symm h)

-- Our aim now is to prove that {u, v} has exactly the two elements e1 and e2 stated above. We can
-- characterise {u, v} by its members (u, v) & (v, u)
lemma characterise_members {u v : V} (e : G.DirEdge) :
G.V_to_Sym2 e = Sym2.mk (u, v) ↔ e.1 = (u, v) ∨ e.1 = (v, u) := by
constructor -- Break into the forward and backward directions
· intro heq1
  have ha : (e.1.1 = u ∧ e.1.2 = v) ∨ (e.1.1 = v ∧ e.1.2 = u) := by
    have : Sym2.mk e.1 = Sym2.mk (u, v) := by
      simpa [V_to_Sym2] using heq1
    exact (sym2_classify (u1 := e.1.1) (v1 := e.1.2) (u2 := u) (v2 := v) this)
  -- We have two separate cases to consider, (↑e).1 = u ∧ (↑e).2 = v, and (↑e).1 = v ∧ (↑e).2 = u
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
· intro heq2
  cases heq2 with
  | inl hpairl =>
    rw [V_to_Sym2, hpairl]
  | inr hpairr =>
    rw [V_to_Sym2, hpairr]
    exact (sym2_comm (u := u) (v := v)).symm

-- While this lemma says that any directed edge that maps to {u, v} must have the pair (u, v) or
-- (v, u), we need actaully show they exist as directed edges in G.DirEdge, and then show that they
-- are distinct. Thus we cna then conclude that the cardinality of the pre-image is 2, i.e that
-- there are exactly 2 directed edges associated to an undirected edge.

-- To begin with this, we need to pick a representative edge . Since we have 'x : ↑(G.UndirEdge)',
-- then we have some x.1 in the range of G.V_to_Sym2, so there exists an edge e with
-- G.V_to_Sym2 e = x.1

noncomputable def chooseDirEdge [Fintype V] (x : ↑(G.UndirEdge)) : G.DirEdge := by
  classical
  have h1 : x.1 ∈ G.UndirEdge := x.property
  -- Recall UndirEdge = Set.range (V_to_Sym2)
  dsimp [UndirEdge] at h1
  have h2 : ∃ e : G.DirEdge, G.V_to_Sym2 e = x.1 :=
    (Set.mem_range).1 h1
  exact Classical.choose h2

-- The above definition says that, given an undirected edge x, pick an edge e that maps to it
-- The following lemma then confirms that the directed edge chosen by the above definition really
-- does map back to x.
lemma chooseDirEdge_maps_back [Fintype V] (x : ↑(G.UndirEdge)) :
G.V_to_Sym2 (G.chooseDirEdge x) = x.1 := by
  classical
  have h1 : x.1 ∈ G.UndirEdge := x.property
  dsimp [UndirEdge] at h1
  have h2 : ∃ e : G.DirEdge, G.V_to_Sym2 e = x.1 :=
    (Set.mem_range).1 h1
  exact Classical.choose_spec h2

-- We will now prove that the cardinality of 'pre_image x' is 2
lemma pre_image_card_eq_2 [Fintype V] (x : ↑(G.UndirEdge)) :
Fintype.card (G.pre_image x) = 2 := by
-- Need classical as we work on the assumption x is in the range of V_to_Sym2
  classical
  set e : G.DirEdge := G.chooseDirEdge x with he_def
  have h : G.V_to_Sym2 e = x.1 := by
    simpa [he_def] using (G.chooseDirEdge_maps_back x)
  -- Unpack the deifnition of e into its vertex pair and adjacency proof
  rcases e with ⟨⟨u, v⟩, huv⟩
  have hx : Sym2.mk (u, v) = x.1 := by
    simpa [V_to_Sym2] using h

  -- Define the elements 'a' and 'b' of the pre-image
  let a : G.pre_image x :=
    ⟨⟨(u, v), huv⟩, by
      simpa [V_to_Sym2] using hx⟩

  let b : G.pre_image x :=
    ⟨⟨(v, u), G.symm huv⟩, by
      have : Sym2.mk (v, u) = x.1 := by
        calc
          Sym2.mk (v, u) = Sym2.mk (u, v) := by
            exact (sym2_comm).symm
          _ = x.1 := hx
      simpa [V_to_Sym2] using this⟩

  -- Can now use loopless to show that a and b are distinct, i.e. if (u, v) = (v, u), then
  -- u = v, contradicting looplessness
  have hneq : a ≠ b := by
    intro heq
    have hdir : (a.1 : G.DirEdge) = b.1 := by
      simpa using congrArg Subtype.val heq
    have hpair : (a.1.1 : V × V) = b.1.1 := by
      simpa using congrArg Subtype.val hdir
    have huv_eq : u = v := by
      exact congrArg Prod.fst hpair
    exact (G.adj_neq huv) huv_eq

  -- We show now that every element of the pre-image is either 'a' or 'b', thus there are at
  -- most 2 elements of the pre-image
  have cover : ∀ y: G.pre_image x, y = a ∨ y = b := by
    intro y
    -- Rewriting in terms of 'u' and 'v' allows me to use the characterisation lemma I proved
    -- earlier, that any directed edge mapping to the unordered pair {u, v} is either (u, v) or
    -- (v, u)
    have hy0 : G.V_to_Sym2 y.1 = Sym2.mk (u, v) := by
      simpa [hx.symm] using y.2
    have hy : y.1.1 = (u, v) ∨ y.1.1 = (v, u) := by
      exact (G.characterise_members (e := y.1)).1 hy0

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
  let e2 : (G.pre_image x) ≃ Fin 2 :=
  { -- First, map a ↦ 0, b ↦ 1
    toFun := fun y =>
      if hya : y = a then (0 : Fin 2) else (1 : Fin 2)
    -- Then the inverse map, 0 ↦ a, 1 ↦ b
    invFun := fun i =>
      if hi0 : i = (0 : Fin 2) then a else b
    --Prove invFun ∘ toFun = id
    left_inv := by
      intro y
      -- We now use the cover lemma to get y = a ∨ b, and separate into cases
      rcases cover y with hya | hyb
      · subst hya
        simp
      · subst hyb
        -- toFun b = 1 (since b ≠ a), invFun 1 = b
        have hba : (b : G.pre_image x) ≠ a := by
          intro h
          exact hneq (h.symm)
        simp [hba]
    -- Prove toFun ∘ invFun = id
    right_inv := by
      intro i
      -- Fin 2 has only 0 or 1, so can split into cases i = 0 or i = 1
      by_cases hi0 : i = (0 : Fin 2)
      · subst hi0
        simp
      · have hi1 : i = (1 : Fin 2) := by
          fin_cases i <;> simp at hi0 ⊢
        subst hi1
        -- show toFun b = 1
        have hbneqa : (b : G.pre_image x) ≠ a := by
          intro h
          exact hneq (h.symm)
        simp [hbneqa, hi0] }

  -- Equivalent finite types have the same cardinality, using card (Fin 2) = 2
  have hcard2 : Fintype.card (G.pre_image x) = Fintype.card (Fin 2) :=
    Fintype.card_congr e2
  simpa using hcard2


-- Now we are done with this, we need to relate it back to the original handshake lemma
-- and conclude the new result. This requires linking the new and old definitions via maps

-- The following definition will map a directed edge to its correpsonding undirected edge
noncomputable
def to_Undir [Fintype V] (e : G.DirEdge) : ↑G.UndirEdge := ⟨G.V_to_Sym2 e, ⟨e, rfl⟩⟩

-- Before proceeding any further, it is important to make the following equivalence:
noncomputable
def pre_image_equiv [Fintype V] (x : ↑(G.UndirEdge)) :
G.pre_image x ≃ {e : G.DirEdge // G.to_Undir e = x} := by
-- We have the functions V_to_Sym2 : DirEdge → Sym2 V, and to_Undir : DirEdge → UndirEdge
-- So while V_to_Sym2 maps directly into Sym2 V, to_Undir instead takes the result as an element
-- of the subtype UndirEdge = Set.range V_to_Sym2. This equivalence identifies that the objects
-- are mathematically the same, the directed edge mapping to a given undirected edge.
  refine
  { toFun := fun y => ⟨y.1, ?_⟩
    invFun := fun y => ⟨y.1, ?_⟩
    left_inv := by
      intro y ; rfl
    right_inv := by
      intro y; rfl }
  · apply Subtype.ext
    simpa [to_Undir] using y.2
  · have : (G.to_Undir y.1 : Sym2 V) = (x : Sym2 V) := congrArg Subtype.val y.2
    simpa [to_Undir] using this

-- We now introduce the lemma that the number of directed edges is twice the number of
-- undirected edges
theorem card_DirEdge_eq_two_card_UndirEdge [Fintype V] :
Fintype.card (G.DirEdge) = 2 * Fintype.card (↑(G.UndirEdge)) := by
  classical
  let f : G.DirEdge → ↑(G.UndirEdge) := G.to_Undir
  -- We will need to introduce sigma for counting. We count all of the pre-images by summing
  -- {e : G.DirEdge // f e = x} over all x : UndirEdge. This takes the disjoint union and then
  -- counts/sums them.
  -- We use Equiv.sigmaFiberEquiv is an equivalence between the domain and the disjoint union of the
  -- 'fibers' (I have used 'pre-image' throughout). This is why we count the pre-images, as
  -- Equiv.sigmaFiberEquiv will conclude this is the same as counting the number of directed edges.
  have hσ : Fintype.card (G.DirEdge) =
  Fintype.card (Σ x : ↑(G.UndirEdge), {e : G.DirEdge // f e = x}) := by
    simpa using (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
  have hsum : Fintype.card (Σ x : ↑(G.UndirEdge), {e : G.DirEdge // f e = x}) =
  ∑ x : ↑(G.UndirEdge), Fintype.card {e : G.DirEdge // f e = x} := by
    simp

  -- We can now use a 'calc' to chain the equalities together
  calc
    Fintype.card (G.DirEdge) = ∑ x : ↑(G.UndirEdge), Fintype.card {e : G.DirEdge // f e = x} := by
      simp [hσ, hsum]
    -- Use the pre_image_equiv lemma to instead consider pre-images I defined earlier instead of
    -- these 'fibers'. We can then use pre_image_cardinality_eq_2 whichs tated each pre-image had
    -- cardinality 2
    _ = ∑ x : ↑(G.UndirEdge), Fintype.card (G.pre_image x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simpa [f] using (Fintype.card_congr (G.pre_image_equiv (x := x))).symm
    -- For each x, we sum over 2 (i.e. each x adds 2 to the sum). We can then show this is
    -- equivalent to simply multiplying the number of undirected edges by 2
    _ = ∑ x : ↑(G.UndirEdge), 2 := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simpa using (G.pre_image_card_eq_2 (x := x))
    _ = 2 * Fintype.card (↑(G.UndirEdge)) := by
      simp
      rw [mul_comm]

-- We have almost everything we need now, but we first need to connect what is in this file to
-- Sean's Simple_Graph_Theory file. To do this, we need to show that 'DirNoEdges = |DirEdges|',
-- bridging the two deifnitions, and then that 'UndirEdgeNum = |UndirEdge|'
-- To do so, we will use a similar ideas as we did previously, write a 'def' using an equivalence.

noncomputable
def DirEdge_equiv_DirEdgeset [Fintype V] : G.DirEdge ≃ ↑(G.DirEdgeset) :=  by
  classical
  refine
  { toFun := fun e => ⟨e.1, ?_⟩
    invFun := fun e => ⟨e.1, ?_⟩
    left_inv := by
      intro e ; rfl
    right_inv := by
      intro e ; rfl }
  · simp
  · aesop

lemma DirNoEdges_eq_card_DirEdge [Fintype V] [DecidableRel G.adj] :
DirNoEdges G = Fintype.card (G.DirEdge) := by
  classical
  -- We first convert DirNoEdges into the cardinality of the subtype ↑(G.DirEdgeset)
  have h1 : G.DirNoEdges = Fintype.card (↑(G.DirEdgeset)) := by
    simp [DirNoEdges]
  have h2 : Fintype.card (↑(G.DirEdgeset)) = Fintype.card (G.DirEdge) := by
    simpa using (Fintype.card_congr (G.DirEdge_equiv_DirEdgeset))
  exact h1.trans h2

-- We now have the undirected version of the statement, that UndirEdgeNum is the cardinality of the
--  subtype ↑(G.UndirEdge)
lemma UndirEdgeNum_eq_card_UndirEdge [Fintype V] [DecidableRel G.adj] :
G.UndirEdgeNum = Fintype.card (↑(G.UndirEdge)) := by
  classical
  simp [UndirEdgeNum]

-- We can finally put this all together and conclude the reuslt of the handshake lemma for
-- undirected graphs. We will rewrite some of the results as hypotheses that we can insert here.
theorem UndirHandshake [Fintype V] [DecidableRel G.adj] :
FinSimpGraph.Degsum G = 2 * G.UndirEdgeNum := by

end SimpGraph
