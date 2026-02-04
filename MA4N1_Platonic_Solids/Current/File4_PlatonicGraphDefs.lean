import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
import MA4N1_Platonic_Solids.Current.File2_DirectedEdgeHandshake
import MA4N1_Platonic_Solids.Current.File3_UndirectedEdgeHandshake



-- Cardinality defintions
def FinGraph.VCard (X : FinGraph) : ℕ :=
    Fintype.card X.VertSet

noncomputable
def FinGraph.ECard (X : FinGraph) : ℕ :=
    UndirEdgeNum X



-- Define a Regular Graph as a Finite Graph with Regularity
structure RegularGraph (X : FinGraph) where
    n : ℕ
    isRegular : ∀ v : X.VertSet, FinGraph.Deg X v = n

-- Define Connected Graph as Simple Graph that is Connected
structure ConnectedGraph {VertSet : Type*} (G : SimpGraph VertSet) where
    isConnected : ∀ u v : VertSet, Relation.ReflTransGen G.adj u v

-- For a platonic graph, we need 3-Connectedness and not just connectedness.
-- To create this structure, we need to do some work first:

-- Take S to be a finite subset of VertSet, and define a new graph with vertex set {v // v ∉ S}
-- i.e. not we take the graph where S has been deleted from the vertex set.
-- Keep the same symmetry, looplessness, adjacency (between leftover vertices only, doesn't keep
-- the edges with any removed vertex as a node)

def SimpGraph.deleteVerts {VertSet : Type*} (G : SimpGraph VertSet) (S : Finset VertSet) :
    SimpGraph {v // v ∉ S} where
        adj u v := G.adj u.1 v.1
        symm := by
            intro u v huv
            exact G.symm huv
        loopless := by
            intro u huu
            exact G.loopless u.1 huu

-- The following is an abstract lemma, kept abstract without inferring much graph theory that we can
-- implement later on. It takes a relation r (for later, will be X.G.adj) and a property p (for
-- later, will be p x := x ∉ S)

-- Essentially, the lemma is telling us 'If there is a path between u and v with adjacency of the
-- graph with vertex set V \ S, then there is a path between the underlying vertices using adjacency
-- of the original graph'.

lemma ReflTransGen_subtype_val {VertSet : Type*} {r : VertSet → VertSet → Prop}
    {p : VertSet → Prop} {u v : {x // p x}} :
    Relation.ReflTransGen (fun a b : {x // p x} => r a.1 b.1) u v →
    Relation.ReflTransGen r u.1 v.1 := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail h₁ h₂ ih =>
      -- h₂ : r (Subtype.val _) (Subtype.val _)
      exact Relation.ReflTransGen.tail ih h₂

-- We now need to define what it means to be 3-Connected, written as a structure.
-- Do we need to say that the size of VertSet is > 3 to make 3-connectedness not be weird????
-- 3-Connected say remocing any two vertices of a connected graph results in the graph remaining
-- connected, so we let S.card < 3. Then apply the adjacency relation on the subgraph.

structure ThreeConnectedGraph (X : FinGraph) where
  isThreeConnected :
    ∀ (S : Finset X.VertSet), S.card < 3 →
      ∀ u v : {x // x ∉ S}, Relation.ReflTransGen (SimpGraph.deleteVerts X.G S).adj u v

-- The following lemma is a sanity check, that 3-Connected still implies connected, so in the
-- definition of platonic graph, we can remove the reuquirement of connected and jsut have
-- 3-connected if we wanted to.
-- It is quite clear that if it is 3-connected, it is connected. If we remain connected after
-- removing vertices, we must have been connected before. We can prove this by taking S = ∅,
-- and then the deleted graph is just the original, which is connected by assumption.

lemma ThreeConnectedGraph.toConnectedGraph (X : FinGraph) (TC : ThreeConnectedGraph X) :
    ConnectedGraph X.G := by
        refine ⟨?_⟩
        intro u v

  -- Let S = ∅, conclude by 3-connectendess that the new graph with V \ S vertex set is connected,
  -- but this is just the graph with vertex set V, i.e. our original graph
        have hdel :=
            TC.isThreeConnected (S := (∅ : Finset X.VertSet)) (by simp) ⟨u, by simp⟩ ⟨v, by simp⟩

        -- Need to actually conclude that the adjacency relation on the graph with nothing removed
        -- is in fact the same adjacency relation we staretd with... 🤬
        have hlift :
            Relation.ReflTransGen
                (fun a b : {x // x ∉ (∅ : Finset X.VertSet)} => X.G.adj a.1 b.1)
                ⟨u, by simp⟩ ⟨v, by simp⟩ := by
            simpa [SimpGraph.deleteVerts] using hdel

        -- Now just forget the subtype and have the underlying path in the original graph. Use the
        -- 'ReflTransGen_subtype_val' lemma with r := X.G.adj and p x := x ∉ ∅
        simpa using
            (ReflTransGen_subtype_val (r := X.G.adj) (p := fun x =>
            x ∉ (∅ : Finset X.VertSet)) hlift)



-- Define Planar Graph as Finite Graph that is Planar (not defined) and has Faces (not defined)
structure PlanarGraph (X : FinGraph) where
    isPlanar : Prop := True

    Face : Type*
    instFace : Fintype Face
    FaceDeg : Face → ℕ

attribute [instance] PlanarGraph.instFace

-- Define the cardinality of the set of faces now we have (somewhat) defined them
def PlanarGraph.FCard {X : FinGraph} (Pl : PlanarGraph X) : ℕ :=
    Fintype.card Pl.Face


noncomputable
def PlanarGraph.FaceDegSum {X : FinGraph} (Pl : PlanarGraph X) : ℕ :=
    ∑ f : Pl.Face, Pl.FaceDeg f


-- here we state Euler's Characteristic Formula but don't prove it. Check `README.md` for more info
theorem PlanarGraph.hEuler (X : FinGraph)
    (Pl : PlanarGraph X) (C : ConnectedGraph X.G) :
    (X.VCard : ℤ) - (X.ECard : ℤ) + (Pl.FCard : ℤ) = 2 := by
        sorry

-- now we have a definition of regularity, we need to show that FinGraph.Degsum X = n*V so we
-- can apply our UndirHandshake theorem
lemma Degsum_eq_n_mul_VCard (X : FinGraph) (R : RegularGraph X) :
    FinGraph.Degsum X = R.n * X.VCard := by
        unfold FinGraph.Degsum
        simp [R.isRegular, FinGraph.VCard]
        apply mul_comm

theorem nV_UndirHandshake (X : FinGraph) (R : RegularGraph X) [DecidableRel X.G.adj] :
    R.n * X.VCard = 2 * UndirEdgeNum X := by
        rw[← Degsum_eq_n_mul_VCard]
        apply UndirHandshake


-- Make a structure for a Platonic Graph. We define it as a Finite, Regular, ThreeConnected,
-- Planar Graph, where each face has the same number of edges which is greater than 2,
-- the degree of each vertex is greater than 2, and each edge lies on the boundary of
-- exactly 2 faces
structure PlatonicGraph where
    -- Bring in strucures we have already defined
    X : FinGraph
    regular : RegularGraph X
    threeConnected : ThreeConnectedGraph X
    planar : PlanarGraph X

    -- Create m
    m : ℕ

    -- Assumption that each face has the same number of edges
    uniformFaces : ∀ f1 f2 : planar.Face, planar.FaceDeg f1 = planar.FaceDeg f2

    -- Define m
    f₀ : planar.Face
    hmdef : m = planar.FaceDeg f₀

    -- Assume m > 2, n > 2 and the set of vertices is not empty
    nonemptyVerts : Nonempty X.VertSet
    hmgt2 : m > 2
    hngt2 : regular.n > 2

    -- This equation states that each edge lies on the boundary of exactly 2 faces.
    -- We are not able to prove this because we do not have a formal definition of a face.
    -- Otherwise, we could just define a graph with the set of vertices as the set of faces
    -- (the dual graph), and then apply UndirHandshake.
    hFaceHandshake : planar.FaceDegSum = 2 * X.ECard


attribute [instance] PlatonicGraph.nonemptyVerts

lemma PlatonicGraph.m_uniform (Pt : PlatonicGraph) :
    ∀ f : Pt.planar.Face, Pt.planar.FaceDeg f = Pt.m := by
        intro f
        simp [hmdef]
        exact Pt.uniformFaces f Pt.f₀


theorem PlatonicGraph.hVerts (Pt : PlatonicGraph) :
    Pt.regular.n * Pt.X.VCard = 2 * Pt.X.ECard := by
        simp [FinGraph.ECard]
        simpa using (nV_UndirHandshake Pt.X Pt.regular)



theorem PlatonicGraph.hFaces (Pt : PlatonicGraph) :
    Pt.m * Pt.planar.FCard = 2 * Pt.X.ECard := by
    classical

    -- Expand FaceDegSum
    have h1 : Pt.planar.FaceDegSum = ∑ f : Pt.planar.Face, Pt.m := by
        -- use uniformFaces to rewrite each FaceDeg f as m
        simp [PlanarGraph.FaceDegSum]
        simp [hmdef]
        simp [PlatonicGraph.m_uniform]

    -- Turn sum of constant into m * number of faces
    have h2 : (∑ f : Pt.planar.Face, Pt.m) = Pt.m * Pt.planar.FCard := by
        simp [PlanarGraph.FCard]
        apply mul_comm

    -- Now combine with the handshake assumption
    calc
        Pt.m * Pt.planar.FCard = ∑ f : Pt.planar.Face, Pt.m := by
            symm
            exact h2
        _ = Pt.planar.FaceDegSum := by
            symm
            exact h1
        _ = 2 * Pt.X.ECard := by
            exact Pt.hFaceHandshake

lemma m_pos_then_E_pos (Pt : PlatonicGraph) : Pt.regular.n > 0 → Pt.X.ECard > 0 := by
    intro hn
    classical

  -- vertices are nonempty because PlanarGraph has nonemptyVerts
    have hV : Pt.X.VCard > 0 := by
        simpa [FinGraph.VCard] using (Fintype.card_pos_iff.mpr Pt.nonemptyVerts)


  -- n * VCard > 0
    have hmul : Pt.regular.n * Pt.X.VCard > 0 :=
        Nat.mul_pos hn hV

  -- rewrite using Pt.hVerts to show 2 * ECard > 0
    have h2E : 2 * Pt.X.ECard > 0 := by
        simpa [Pt.hVerts] using hmul
    simpa [mul_comm] using h2E
