import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import MA4N1_Platonic_Solids.Old.Inequality_Derivation_Lemmas
open Inequality_Derivation_Lemmas

-------------
-- THEOREM --
-------------
-- WHAT: Deriving (m-2)(n-2)<4 from the definition of a Platonic Solid
-- USING: Lemmas constructed in MA4N1_Platonic_Solids.Inequality_Derivation_Lemmas
theorem platonic_inequality

  -- Variables
  {V E F m n : ℝ}

  -- Hypotheses
  (hm : m > 0)
  (hn : n > 0)
  (hE : E > 0)
  (hEuler : V - E + F = 2)
  (hFaces : m * F = 2 * E)
  (hVerts : n * V = 2 * E) :

  -- Claim
  (m - 2) * (n - 2) < 4 := by

-----------
-- PROOF --
-----------

-- Define new hypotheses: m, n, and E are not 0
have hm' : m ≠ 0 := by linarith [hm]
have hn' : n ≠ 0 := by linarith [hn]
have hE' : E ≠ 0 := by linarith [hE]

-- Define new hypotheses: Rearrange hFaces and hVerts by dividing both sides by m or n respectively
have hF : F = 2 * E / m := by rw[← rearr_Faces_Verts (hFaces) (hm')]
have hV : V = 2 * E / n := by rw[← rearr_Faces_Verts (hVerts) (hn')]

-- Define new hypothesis: Multiply both sides of hEuler by mn/E
have hEuler_div_E :  n * m * (V - E + F) / E = n * m * 2 / E := by rw[hEuler]

-- Sub hF and hV into hEuler_div_E to remove V and F
rw[hF, hV] at hEuler_div_E

-- Simplify hEuler_div_E
rw[rearr_hEuler_lhs (hn') (hm') (hE')] at hEuler_div_E
rw[rearr_hEuler_rhs] at hEuler_div_E

-- Define new hypothesis: RHS of hEuler_div_E is greater than 0
have h_rhs_pos : 2 * (n * (m * E⁻¹)) > 0 := by
  have mE_inv_pos : m * E⁻¹ > 0 := mul_pos (hm) (inv_pos.mpr hE)
  have nmE_inv_pos : n * (m * E⁻¹) > 0 := mul_pos (hn) (mE_inv_pos)
  exact mul_pos (by norm_num) (nmE_inv_pos)

-- Flipping hEuler_div_E and h_rhs_pos so that tactics can be applied
symm at hEuler_div_E
apply gt_iff_lt.mp at h_rhs_pos

-- Define new hypothesis: LHS of hEuler_div_E is greater than 0
have h_lhs_pos : 2 * m + -(n * m) + 2 * n > 0 :=
  lt_of_lt_of_eq h_rhs_pos hEuler_div_E

-- Flip and double negate h_lhs_pos so that tactics can be applied
apply gt_iff_lt.mp at h_lhs_pos
rw[← neg_neg (2*m+-(n*m)+2*n)] at h_lhs_pos

-- Define new hypothesis: Negating boths sides of h_lhs_pos and flipping inequality
have h_neg_lhs_neg :
  -(2 * m + -(n * m) + 2 * n) < 0 := neg_pos.mp h_lhs_pos

-- Rearranging h_neg_lhs_neg to be more readable
rw[rearr_h_neg_lhs_neg] at h_neg_lhs_neg

-- Define new hypothesis: Add 4 to both sides of h_neg_lhs_neg
have h_neg_lhs_neg_add_four :
  n * m + -(2 * n) + -(2 * m) + 4 < 0 + 4 := add_lt_add_right h_neg_lhs_neg 4

-- Getting rid of 0 from h_neg_lhs_neg_add_four
rw[zero_add] at h_neg_lhs_neg_add_four

-- Define new hypothesis: Factorise h_neg_lhs_neg_add_four
have h_factor :
  n * m + -(2 * n) + -(2 * m) + 4 = (m - 2) * (n - 2) := by ring

-- Flip h_factor so tactic can be applied
symm at h_factor

-- Putting h_factor and h_neg_lhs_neg_add_four together gives us
-- the final inequality which we can apply
apply lt_of_eq_of_lt h_factor h_neg_lhs_neg_add_four
