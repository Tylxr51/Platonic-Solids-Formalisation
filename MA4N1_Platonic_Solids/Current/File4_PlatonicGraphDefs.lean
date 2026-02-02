import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
import MA4N1_Platonic_Solids.Current.File2_DirectedEdgeHandshake
import MA4N1_Platonic_Solids.Current.File3_UndirectedEdgeHandshake




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

-- Define Planar Graph as Finite Graph that is Planar (not defined), has Faces, and
-- has V - E + F = 2. We do not define planarity as it is out of the scope of this project,
-- so we simply state is as a property
structure PlanarGraph (X : FinGraph) where
    isPlanar : Prop := True

    Face : Type*
    instFace : Fintype Face
    FaceDeg : Face → ℕ


attribute [instance] PlanarGraph.instFace

def PlanarGraph.FCard {X : FinGraph} (Pl : PlanarGraph X) : ℕ :=
    Fintype.card Pl.Face

noncomputable
def PlanarGraph.FaceDegSum {X : FinGraph} (Pl : PlanarGraph X) : ℕ :=
    ∑ f : Pl.Face, Pl.FaceDeg f


theorem PlanarGraph.hEuler (X : FinGraph) (Pl : PlanarGraph X) :
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



structure PlatonicGraph where
    X : FinGraph
    regular : RegularGraph X
    connected : ConnectedGraph X.G
    planar : PlanarGraph X

    m : ℕ
    uniformFaces : ∀ f : planar.Face, planar.FaceDeg f = m

    hFaceHandshake : planar.FaceDegSum = 2 * X.ECard


    -- hFaces : m * planar.FCard = 2 * planar.ECard


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
        simp [PlanarGraph.FaceDegSum, Pt.uniformFaces]

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
