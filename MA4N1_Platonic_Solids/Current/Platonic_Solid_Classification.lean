import Mathlib.Tactic.IntervalCases
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





-- Defining a map from the pair (m,n) to its associated platonic solid, and return
-- 'none' for other pairs
def mn_solid : (ℕ × ℕ) → String
| (3, 3) => "Tetrahedron"
| (3, 4) => "Octahedron"
| (3, 5) => "Icosahedron"
| (4, 3) => "Cube"
| (5, 3) => "Dodecahedron"
| _      => "None"


-- Now name the Platonic Graph by looking at its pair (m, n)
def PlatonicSolid (Pt : PlatonicGraph) : String :=
  mn_solid (Pt.m, Pt.regular.n)







theorem classify_Pt_mn_members (Pt : PlatonicGraph) (hmgt2 : Pt.m > 2) (hngt2 : Pt.regular.n > 2) :
  (Pt.m, Pt.regular.n) ∈ PlatonicPairs := by
  have hR :
    ((Pt.m : ℝ) - 2) * ((Pt.regular.n : ℝ) - 2) < 4 := platonic_inequality Pt hmgt2 hngt2

  -- cast the above hR to the naturals ℕ
  have hN : (Pt.m - 2) * (Pt.regular.n - 2) < 4 :=
    nat_ineq_of_real_ineq Pt.m Pt.regular.n hmgt2 hngt2 hR

  -- membership in the LHS set of classify_mn
  have hmem :
    (Pt.m, Pt.regular.n) ∈
      ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4}) := by
    exact ⟨hmgt2, hngt2, hN⟩

  simpa [PlatonicPairs, classify_mn] using hmem

def PlatonicSolidNames : Set String :=
  ({"Tetrahedron", "Octahedron", "Icosahedron", "Cube", "Dodecahedron"} : Set String)

theorem classify_Pt_name_mem (Pt : PlatonicGraph) (hmgt2 : Pt.m > 2) (hngt2 : Pt.regular.n > 2) :
  PlatonicSolid Pt ∈ PlatonicSolidNames := by
    have hmem : (Pt.m, Pt.regular.n) ∈ PlatonicPairs :=
      classify_Pt_mn_members Pt hmgt2 hngt2

    have hc :
      (Pt.m, Pt.regular.n) = (3, 3) ∨
      (Pt.m, Pt.regular.n) = (3, 4) ∨
      (Pt.m, Pt.regular.n) = (3, 5) ∨
      (Pt.m, Pt.regular.n) = (4, 3) ∨
      (Pt.m, Pt.regular.n) = (5, 3) := by
        simpa [PlatonicPairs, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

    unfold PlatonicSolid PlatonicSolidNames
    rcases hc with h | h | h | h | h <;> simp [mn_solid, h]
