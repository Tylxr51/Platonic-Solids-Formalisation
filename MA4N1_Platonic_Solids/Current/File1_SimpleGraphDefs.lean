import Mathlib.Logic.Basic
import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset



structure SimpGraph (V : Type*) where
    (adj : V → V → Prop)
    (symm : Symmetric adj)
    (loopless : Irreflexive adj)

structure FinGraph where
    VertSet : Type*
    instVertSet : Fintype VertSet
    G : SimpGraph VertSet


-- make an instance of instV
attribute [instance] FinGraph.instVertSet


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
instance FinGraph.FinAdjEdgeset (X : FinGraph) (v : X.VertSet) :
    Fintype ↑(X.G.AdjEdgeset v) := by
    have h1 : (X.G.AdjEdgeset v).Finite := by
        unfold SimpGraph.AdjEdgeset
        simp only
        unfold SimpGraph.Nbhd
        simp only [Set.mem_setOf_eq]
        exact Set.finite_univ.subset (by intro x hx; trivial)
    exact h1.fintype

-- I needed to be able to convert the adjacent edgeset to a finset for our
-- argument in the case that V is finite. That is what this defintion does
noncomputable
def FinGraph.AdjEdgeFinset (X : FinGraph) (v : X.VertSet) :
    Finset (X.VertSet × X.VertSet) :=
    (X.G.AdjEdgeset v).toFinset

-- Typically, the degree might be defined as the cardinality of the neighbourhood
-- but it is easy to see that this definition is equivalent.
-- It would also be possible to generalise this definition to locally finite
-- graphs, but that was beyond the scope of the project.
noncomputable
def FinGraph.Deg (X : FinGraph) (v : X.VertSet) : ℕ :=
    Finset.card (FinGraph.AdjEdgeFinset X v)

-- Degsum is the sum of the degrees #wow
noncomputable
def FinGraph.Degsum (X : FinGraph) : ℕ :=
  ∑ v : X.VertSet, FinGraph.Deg X v
