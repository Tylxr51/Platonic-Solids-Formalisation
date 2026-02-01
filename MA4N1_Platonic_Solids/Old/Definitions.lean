import Mathlib.Tactic
import MA4N1_Platonic_Solids.Old.Simple_Graph_Theory

-- Added by Sean
def PlatonicSolids : Set (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  { p |
    let V := p.1
    let E := p.2.1
    let F := p.2.2.1
    let m := p.2.2.2.1
    let n := p.2.2.2.2
    V - E + F = 2 ∧ m * F = 2 * E ∧ n * V = 2 * E }
