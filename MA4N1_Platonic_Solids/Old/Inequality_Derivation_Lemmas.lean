import Mathlib.Tactic

namespace Inequality_Derivation_Lemmas


----------------------------------------------------------------------------------------------------
-----------
-- LEMMA --
-----------
-- WHAT: Divides both sides of hFaces and hVerts by m and n respectively
-- USING: Mathlib.Algebra
lemma rearr_Faces_Verts

  -- Variables
  {A b E : ℝ}

  -- Hypotheses
  (hEuler : b * A = 2 * E)
  (hb : b ≠ 0) :

  -- Claim
  A = 2 * E / b := by

-----------
-- PROOF --
-----------

rw[← hEuler]
rw[mul_comm]
rw[mul_div_cancel_right₀ A hb]
----------------------------------------------------------------------------------------------------

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%--

----------------------------------------------------------------------------------------------------
-----------
-- LEMMA --
-----------
-- WHAT: Simplifies hEuler_div_E lhs
-- USING: Mathlib.Algebra
lemma rearr_hEuler_lhs

  -- Variables
  {n m E : ℝ}

  -- Hypothesis
  (hn' : n ≠ 0)
  (hm' : m ≠ 0)
  (hE' : E ≠ 0) :

  -- Claim
  n * m * (2 * E / n - E + 2 * E / m) / E = 2 * m + -(n * m) + 2 * n := by

-----------
-- PROOF --
-----------

-- Change all divides to inverses (easier to stick to multiplicative tactics)
repeat rw [div_eq_mul_inv]

-- Distribute E⁻¹ and cancel
rw[sub_eq_add_neg, mul_assoc, right_distrib, right_distrib]
rw[mul_assoc 2 E n⁻¹, mul_assoc 2 (E*n⁻¹) E⁻¹, mul_comm (E*n⁻¹), ← mul_assoc E⁻¹, mul_comm E⁻¹]
rw[← neg_mul_eq_neg_mul]
rw[mul_assoc 2 E m⁻¹, mul_assoc 2 (E*m⁻¹), mul_comm (E*m⁻¹), ←mul_assoc E⁻¹, mul_comm E⁻¹]
repeat rw[mul_inv_cancel₀ hE']
repeat rw[one_mul]

-- Distribute n and cancel
rw[mul_assoc, mul_comm, mul_assoc, right_distrib, right_distrib]
rw[←neg_mul_eq_neg_mul, one_mul]
rw[mul_assoc 2, mul_comm n⁻¹]
rw[mul_inv_cancel₀ hn', mul_one]

-- Distribute m and cancel
rw[left_distrib, left_distrib]
repeat rw[← mul_assoc m]
rw[mul_comm m, mul_assoc 2 m]
repeat rw[mul_inv_cancel₀ hm']
rw[mul_one]

-- Rearrange middle term
rw[mul_comm m, ←neg_mul_eq_neg_mul]
----------------------------------------------------------------------------------------------------

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%--

----------------------------------------------------------------------------------------------------
-----------
-- LEMMA --
-----------
-- WHAT: Simplifies hEuler_div_E rhs
-- USING: Mathlib.Algebra

lemma rearr_hEuler_rhs

  -- Variables
  {n m E : ℝ} :

  -- Claim
  n * m * 2 / E = 2 * (n * (m / E)) := by

-----------
-- PROOF --
-----------
rw[mul_assoc n m 2, mul_comm m 2, ← mul_assoc, mul_comm n 2]
rw[mul_assoc, mul_div_assoc, mul_div_assoc]
----------------------------------------------------------------------------------------------------

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%--

----------------------------------------------------------------------------------------------------
-----------
-- LEMMA --
-----------
-- WHAT: Simplifies hEuler_div_E rhs
-- USING: Mathlib.Algebra

lemma rearr_h_neg_lhs_neg

  -- Variables
  {n m : ℝ} :

  -- Claim
  -(2 * m + -(n * m) + 2 * n) = n * m + -(2 * n) + -(2 * m) := by

-----------
-- PROOF --
-----------
rw[neg_add, neg_add, neg_neg, ← neg_mul, add_comm, ← add_assoc, add_comm, ← add_assoc, neg_mul]
----------------------------------------------------------------------------------------------------

end Inequality_Derivation_Lemmas
