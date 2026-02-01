import Mathlib.Tactic.IntervalCases

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

/- Final classification theorem for the pairs (m, n) -/
theorem classify_mn : ({(m, n) : ℕ × ℕ | m > 2 ∧ n > 2 ∧ (m - 2) * (n - 2) < 4})
 = {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} := by
  rw [← shift, shift_classify]
  ext
  aesop

/- Defining a map from the pair (m,n) to its associated
platonic solid, and return 'none' for other pairs -/
def mn_solid : (ℕ × ℕ) → String
| (3, 3) => "Tetrahedron"
| (3, 4) => "Octahedron"
| (3, 5) => "Icosahedron"
| (4, 3) => "Cube"
| (5, 3) => "Dodecahedron"
| _      => "None"

/- Examples to check definition works -/
#eval mn_solid (3, 5)
#eval mn_solid (6, 6)
