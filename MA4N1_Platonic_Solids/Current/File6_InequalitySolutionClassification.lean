import Mathlib.Tactic.IntervalCases
import MA4N1_Platonic_Solids.Current.File4_PlatonicGraphDefs
import MA4N1_Platonic_Solids.Current.File5a_InequalityDerivationTheorem


-- This file classifies the pairs (m, n) that arise from `PlatonicGraph`, proves that there are
-- only five possibilities, and then maps each to its associated named Platonic graph.


-- We shift the solution set down to avoid subtraction in ℕ.
lemma shift_classify : {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4}
 = {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)} := by
  ext x
  aesop
  have : fst < 3 := by
    grind
  interval_cases fst
  · grind
  · grind
  · grind

-- Intermediate lemma: With the added restrictions on m and n, shifting the solution set up by
-- (3, 3) is an equivalent statement.
lemma shift : (· + (3,3)) '' {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4}
 = {(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} := by
  ext x
  aesop
  use fst - 3, snd - 3
  obtain _|_|_|fst := fst <;> try grind
  obtain _|_|_|snd := snd <;> grind

-- Defining `PlatonicPairs` to be the solution set, avoiding continuously rewriting out the set.
-- They are the five possible pairs arising from the inequalities for a `PlatonicGraph`.
def PlatonicPairs : Set (ℕ × ℕ) := {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}

-- Classification theorem for the pairs defined by the inequalities provided.
theorem classify_mn : ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
  = PlatonicPairs := by
    have h :
        ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
          = ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Set (ℕ × ℕ)) := by
      rw [← shift, shift_classify]
      ext x
      aesop
    simpa [PlatonicPairs] using h

-- Corollary: any `PlatonicGraph` has (Pt.m, Pt.regular.n) in `PlatonicPairs`.
-- This adds context to (m, n), by setting m = Pt.m and n = Pt.regular.n
theorem classify_Pt_mn_members (Pt : PlatonicGraph) : (Pt.m, Pt.regular.n) ∈ PlatonicPairs := by
  have hmem :
    (Pt.m, Pt.regular.n) ∈
      ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4}) := by
    exact ⟨Pt.hmgt2, Pt.hngt2, platonic_inequality Pt⟩
  simpa [classify_mn] using hmem


-- Map a pair (m, n) to its corresponding named `PlatonicGraph`
-- The names correspond to the classical Platonic solids, justified externally via Steinitz’s
-- Theorem as explained in the README.md file. This is a conventional labeling, not an additional
-- formal result.
def mn_graph_name : (ℕ × ℕ) → String
| (3, 3) => "Tetrahedron Graph"
| (3, 4) => "Octahedron Graph"
| (3, 5) => "Icosahedron Graph"
| (4, 3) => "Cube Graph"
| (5, 3) => "Dodecahedron Graph"
| _      => "[Not a Platonic Graph]"

-- This is the set of names obtained from the classified `PlatonicPairs`. We encode these names in
-- the set PlatonicGraphNames of strings in order to avoid having to rewrite inside the final
-- theorem, and maintain readability.
def PlatonicGraphNames : Set String :=
  mn_graph_name '' PlatonicPairs


-- This is the final classification, combining the previous theorem and the mapping to a named
-- Platonic graph. That is, "Any `PlatonicGraph` corresponds to one of the five named Platonic
-- Graphs"
theorem classify_Pt_name_mem (Pt : PlatonicGraph) :
  mn_graph_name (Pt.m, Pt.regular.n) ∈ PlatonicGraphNames := by
    have hmem : (Pt.m, Pt.regular.n) ∈ PlatonicPairs :=
      classify_Pt_mn_members Pt

    unfold PlatonicGraphNames
    refine ⟨(Pt.m, Pt.regular.n), hmem, rfl⟩

-- We can check that we have in fact mapped each element of `PlatonicPairs` (m, n) to a named
-- `PlatonicGraph`. Although our formalisation works entirely at the level of graphs
-- (see README.md), each pair is mapped to its classical Platonic solid graph, and as such the name
-- reflects this.
#eval mn_graph_name (3,5)
#eval mn_graph_name (4,3)
#eval mn_graph_name (5,6)
