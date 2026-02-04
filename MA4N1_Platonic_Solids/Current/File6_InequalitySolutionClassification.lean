import Mathlib.Tactic.IntervalCases
import MA4N1_Platonic_Solids.Current.File4_PlatonicGraphDefs
import MA4N1_Platonic_Solids.Current.File5a_InequalityDerivationTheorem


/- Shifting the solution set down to avoid subtraction in ℕ -/
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

/- Function to shift the set back to what we desire -/
lemma shift : (· + (3,3)) '' {(m, n) : ℕ × ℕ | (m + 1) * (n + 1) < 4}
 = {(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4} := by
  ext x
  aesop
  use fst - 3, snd - 3
  obtain _|_|_|fst := fst <;> try grind
  obtain _|_|_|snd := snd <;> grind


def PlatonicPairs : Set (ℕ × ℕ) := {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}

-- Final classification theorem for the pairs (m, n), as PlatonicPairs for readability
theorem classify_mn :
    ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
      = PlatonicPairs := by
  -- The following proves it equals the set explicitly
  have h :
      ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
        = ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Set (ℕ × ℕ)) := by
    rw [← shift, shift_classify]
    ext x
    aesop
  simpa [PlatonicPairs] using h


theorem classify_Pt_mn_members (Pt : PlatonicGraph) :
  (Pt.m, Pt.regular.n) ∈ PlatonicPairs := by

  -- membership in the LHS set of classify_mn
  have hmem :
    (Pt.m, Pt.regular.n) ∈
      ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4}) := by
    exact ⟨Pt.hmgt2, Pt.hngt2, platonic_inequality Pt⟩

  simpa [PlatonicPairs, classify_mn] using hmem


-- Defining a map from the pair (m,n) to its associated platonic solid, and return
-- '[Not a Platonic Graph]' for other pairs
def mn_graph_name : (ℕ × ℕ) → String
| (3, 3) => "Tetrahedron Graph"
| (3, 4) => "Octahedron Graph"
| (3, 5) => "Icosahedron Graph"
| (4, 3) => "Cube Graph"
| (5, 3) => "Dodecahedron Graph"
| _      => "[Not a Platonic Graph]"


def PlatonicGraphNames : Set String :=
  mn_graph_name '' PlatonicPairs

theorem classify_Pt_name_mem (Pt : PlatonicGraph) :
  mn_graph_name (Pt.m, Pt.regular.n) ∈ PlatonicGraphNames := by
    have hmem : (Pt.m, Pt.regular.n) ∈ PlatonicPairs :=
      classify_Pt_mn_members Pt

    unfold PlatonicGraphNames
    refine ⟨(Pt.m, Pt.regular.n), hmem, rfl⟩
