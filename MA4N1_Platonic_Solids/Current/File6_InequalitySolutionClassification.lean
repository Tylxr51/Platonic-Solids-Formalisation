import Mathlib.Tactic.IntervalCases
import MA4N1_Platonic_Solids.Current.File4_PlatonicGraphDefs
import MA4N1_Platonic_Solids.Current.File5a_InequalityDerivationTheorem


-- This file classifies the pairs (m, n) that arise from the definition of PlatonicGraph, proves
-- that there are only 5 possibilities, and then maps each to its associated named Platonic graph.


-- We shift the solution set down to avoid subtraction in ℕ.
lemma shift_classify : {(m, n) : ℕ × ℕ | (m + 1) * (n + 1)< 4}
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

-- Defining PlatonicPairs to be the the solution set, avoiding continuously rewriting out the set.
-- They are the 5 possible pairs arising from the definition of a PlatonicGraph.
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



-- We now add context to what (m, n) are now. That is, for any PlatonicGraph, its associated pair
-- (Pt.m, Pt.regular.n) lie in the set PlatonicPairs. Pt.m and Pt.regular.n encode the inequalities
-- in the previous classification, so this is a trivial corollary.
theorem classify_Pt_mn_members (Pt : PlatonicGraph) : (Pt.m, Pt.regular.n) ∈ PlatonicPairs := by
  have hmem :
    (Pt.m, Pt.regular.n) ∈
      ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4}) := by
    exact ⟨Pt.hmgt2, Pt.hngt2, platonic_inequality Pt⟩
  simpa [classify_mn] using hmem


-- Map a pair (m, n) to its corresponding named PlatonicGraph.
def mn_graph_name : (ℕ × ℕ) → String
| (3, 3) => "Tetrahedron Graph"
| (3, 4) => "Octahedron Graph"
| (3, 5) => "Icosahedron Graph"
| (4, 3) => "Cube Graph"
| (5, 3) => "Dodecahedron Graph"
| _      => "[Not a Platonic Graph]"

-- This is the set of names obtained from the classified PlatonicPairs. We encode these names in the
-- set string PlatonicGraphNames in order to avoid having to rewrite inside the final theorem, and
-- maintain readability.
def PlatonicGraphNames : Set String :=
  mn_graph_name '' PlatonicPairs


-- This is the final classification, combining the previous theorem and the mapping to a named
-- Platonic Graph. That is, 'Any PlatonicGraph corresponds to one of the five named Platonic Graphs'
theorem classify_Pt_name_mem (Pt : PlatonicGraph) :
  mn_graph_name (Pt.m, Pt.regular.n) ∈ PlatonicGraphNames := by
    have hmem : (Pt.m, Pt.regular.n) ∈ PlatonicPairs :=
      classify_Pt_mn_members Pt

    unfold PlatonicGraphNames
    refine ⟨(Pt.m, Pt.regular.n), hmem, rfl⟩
