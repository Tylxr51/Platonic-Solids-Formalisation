import Mathlib.Tactic.Linarith
import MA4N1_Platonic_Solids.Current.File1_SimpleGraphDefs
import MA4N1_Platonic_Solids.Current.File2_DirectedEdgeHandshake
import MA4N1_Platonic_Solids.Current.File3_UndirectedEdgeHandshake
import MA4N1_Platonic_Solids.Current.File4_PlatonicGraphDefs
import MA4N1_Platonic_Solids.Current.File5b_InequalityDerivationLemmas




theorem platonic_inequality

  (Pt : PlatonicGraph)

  (hmgt2 : Pt.m > 2)
  (hngt2 : Pt.regular.n > 2) :

  ((Pt.m : ℝ) - 2) * ((Pt.regular.n : ℝ) - 2) < 4 := by


  ------------------------------------------------------------------------------

  -- set up shorthand (NAT)
  let m : ℝ := Pt.m
  let n : ℝ := Pt.regular.n
  let V : ℝ := Pt.X.VCard
  let E : ℝ := Pt.X.ECard
  let F : ℝ := Pt.planar.FCard

  -- now define REAL versions


  change (m - 2) * (n - 2) < 4

  -- get real equations
  have hFacesR : (Pt.m : ℝ) * (Pt.planar.FCard : ℝ) = 2 * (Pt.X.ECard : ℝ) := by
    exact_mod_cast Pt.hFaces

  have hVertsR : (Pt.regular.n : ℝ) * (Pt.X.VCard : ℝ) = 2 * (Pt.X.ECard : ℝ) := by
    exact_mod_cast Pt.hVerts

  have hFaces : m * F = 2 * E := by
    simpa [m, F, E] using hFacesR

  have hVerts : n * V = 2 * E := by
    simpa [n, V, E] using hVertsR

  have hEuler : V - E + F = 2 := by
    have hEulerZ : (Pt.X.VCard : ℤ) - (Pt.X.ECard : ℤ) + (Pt.planar.FCard : ℤ) = 2 :=
      PlanarGraph.hEuler Pt.X Pt.planar
    have := congrArg (fun z : ℤ => (z : ℝ)) hEulerZ
    -- this `simp` should turn `(VN : ℤ : ℝ)` into `(VN : ℝ)` etc
    simpa [V, E, F] using this

  have hEposPt : Pt.X.ECard > 0 :=
    m_pos_then_E_pos Pt (lt_trans (by decide : (0 : ℕ) < 2) hngt2)

  -- positivity / nonzero in ℝ
  have hmpos : m > 0 := by
    -- hm : mN > 2
    have : m > 0 := by
      simp [m]
      exact_mod_cast lt_trans (by decide : (0 : ℕ) < 2) hmgt2
    simpa [m] using this

  have hnpos : n > 0 := by
    have : n > 0 := by
      simp [n]
      exact_mod_cast lt_trans (by decide : (0 : ℕ) < 2) hngt2
    simpa [n] using this

  have hEpos : E > 0 := by
    have : E > 0 := by
      simp [E]
      exact_mod_cast hEposPt
    simpa [E] using this

  -- From positivity get nonzero facts
  have hm' : m ≠ 0 := by linarith [hmpos]
  have hn' : n ≠ 0 := by linarith [hnpos]
  have hE' : E ≠ 0 := by linarith [hEpos]

  -- loads of errors from this point on

  -- Rearrange faces and verts using algebraic lemmas
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
    have mE_inv_pos : m * E⁻¹ > 0 := mul_pos (by linarith [hmpos]) (inv_pos.mpr hEpos)
    have nmE_inv_pos : n * (m * E⁻¹) > 0 := mul_pos (by linarith [hnpos]) mE_inv_pos
    exact mul_pos (by norm_num) nmE_inv_pos

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



-- Changed variables to be in ℝ, but to connect to Platonic classification, might need a
-- lemma that casts them to the naturals
-- Just general lemmas at the moment, not relating to Platonic Graphs so will keep as just hm and hn
-- instead of writing hmgt2 and hngt2
lemma cast_sub_two (m : ℕ) (hm : m > 2) : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
  simpa using (Nat.cast_sub (le_of_lt hm) : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - (2 : ℝ))

lemma nat_ineq_of_real_ineq
  (m n : ℕ) (hm : m > 2) (hn : n > 2) (hR : ((m : ℝ) - 2) * ((n : ℝ) - 2) < 4) :
  (m - 2) * (n - 2) < 4 := by
    have h1 :
        ((m - 2 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) < 4 := by
      simpa [cast_sub_two m hm, cast_sub_two n hn] using hR

    have h2 : (((m - 2) * (n - 2) : ℕ) : ℝ) < 4 := by
      simpa [Nat.cast_mul] using h1

    exact_mod_cast h2
