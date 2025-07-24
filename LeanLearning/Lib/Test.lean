import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

open RealInnerProductSpace

notation "ℝ^{" n "}" => EuclideanSpace ℝ (Fin n)
variable {n : ℕ} (a : ℝ) (x y : ℝ^{n})

theorem cauchy_schwarz_concrete : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  exact abs_real_inner_le_norm x y

lemma inner_prod_over_mag (h : a ≠ 0) : (a / ‖a‖) * (a / ‖a‖) = 1 := by
  field_simp [h]

lemma simp_mul_inv (hx : ‖x‖ ≠ 0) : 1 / ‖x‖ * (1 / ‖x‖) = 1 / ‖x‖ ^ 2 := by
  field_simp [hx]
  ring

lemma simp_mul_with_coeff (hy : ‖y‖ ≠ 0) : a • (1 / ‖y‖) * a • (1 / ‖y‖) = a^2 * (1 / ‖y‖^2) := by
  rw [smul_eq_mul, mul_one_div]
  field_simp
  rw [←pow_two a, pow_two ‖y‖]

lemma get_one (v : ℝ^{n}) (h : ⟪v, v⟫ ≠ 0): 1 / ‖v‖ * (1 / ‖v‖) * ⟪v, v⟫ = 1 :=  by
  rw [mul_assoc, one_div_mul_eq_div, one_div_mul_eq_div, div_div, norm_eq_sqrt_real_inner]
  rw [←pow_two, Real.sq_sqrt (real_inner_self_nonneg), div_self]
  exact h

lemma nonzero_inner_implies_nonzero_vectors (h : ⟪x, y⟫ ≠ 0) : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, inner_zero_left] at h
    exact h rfl
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, inner_zero_right] at h
    exact h rfl
  exact ⟨inner_self_ne_zero.mpr hx, inner_self_ne_zero.mpr hy⟩

lemma nonzero_inner_implies_nonzero_mag (h : ⟪x, y⟫ ≠ 0) : ‖x‖ > 0 ∧ ‖y‖ > 0 := by
  apply And.intro
  . by_contra hx
    by_cases hx_lt0: ‖x‖ < 0
    -- ‖x‖ < 0
    . have : ‖x‖ ≥ 0 := by exact norm_nonneg x
      linarith
    -- ‖x‖ ≥ 0
    . have : ‖x‖ = 0 := by linarith
      have : x = 0 := by exact norm_eq_zero.mp this
      rw [this, inner_zero_left] at h
      contradiction
  . by_contra hy
    by_cases hx_lt0: ‖y‖ < 0
    -- ‖y‖ < 0
    . have : ‖y‖ ≥ 0 := by exact norm_nonneg y
      linarith
    -- ‖y‖ ≥ 0
    . have : ‖y‖ = 0 := by linarith
      have : y = 0 := by exact norm_eq_zero.mp this
      rw [this, inner_zero_right] at h
      contradiction


theorem cauchy_schwarz : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  by_cases hxy : ‖⟪x, y⟫‖ = 0
  . rw [hxy]
    refine Left.mul_nonneg ?_ ?_
    <;> apply norm_nonneg
  . let α := ⟪x, y⟫ / ‖⟪x, y⟫‖

    have ha : 0 ≤ ⟪‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y, ‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y⟫ := real_inner_self_nonneg
    rw [inner_sub_sub_self] at ha
    repeat rw [real_inner_smul_left, real_inner_smul_right] at ha
    rw [real_inner_comm x y] at ha
    repeat rw [← mul_assoc] at ha
    rw [mul_comm ‖x‖⁻¹ (α • ‖y‖⁻¹)] at ha

    let a : ℝ := ⟪x, y⟫
    have hnxy : a ≠ 0 := mt (λ h => norm_eq_zero.mpr h) hxy
    have h1 : α ^ 2 = 1 := Eq.trans (pow_two α) (inner_prod_over_mag a hnxy)

    have hxhy : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := nonzero_inner_implies_nonzero_vectors x y hnxy
    have hnxhny : ‖x‖ > 0 ∧ ‖y‖ > 0 := nonzero_inner_implies_nonzero_mag x y hnxy
    have : 1 / ‖y‖ ^ 2 = 1 / ‖y‖ * (1 / ‖y‖) := by rw [one_div_mul_one_div, pow_two]

    have hny : ‖y‖ > 0 := hnxhny.right
    have y_mag_ne_zero : ‖y‖ ≠ 0 := by
      rw [gt_iff_lt] at hny
      exact Ne.symm (ne_of_lt hny)

    rw [inv_eq_one_div ‖x‖, inv_eq_one_div ‖y‖, simp_mul_with_coeff α y y_mag_ne_zero] at ha
    rw [h1, one_mul, smul_eq_mul, this] at ha
    rw [get_one x hxhy.left, get_one y hxhy.right] at ha

    field_simp only [hnxhny.left, hnxhny.right, mul_one] at ha
    have non_neg : ‖y‖ * ‖x‖ > 0 := by apply Left.mul_pos hnxhny.right hnxhny.left
    have combine_same : - α * ⟪x, y⟫ / (‖y‖ * ‖x‖) - α * ⟪x, y⟫ / (‖y‖ * ‖x‖) = -2 * α * ⟪x, y⟫ / (‖y‖ * ‖x‖) := by
      field_simp only [non_neg]
      ring_nf
    ring_nf at ha

    have two_positive : (0 : ℝ) ≤ 2 := by linarith
    have h_div: 0 ≤ (2 - α * ⟪x, y⟫ * ‖y‖⁻¹ * ‖x‖⁻¹ * 2) / 2 :=
      div_nonneg ha two_positive
    have h_simp : 0 ≤ 1 - ⟪x, y⟫ / ‖⟪x, y⟫‖ * ⟪x, y⟫ * ‖y‖⁻¹ * ‖x‖⁻¹ := by
      rw [sub_div, mul_div_assoc, div_self (two_ne_zero), mul_one] at h_div
      exact h_div
    rw [div_eq_inv_mul] at h_simp
    have : ⟪x, y⟫ * ⟪x, y⟫ = |⟪x, y⟫| * |⟪x, y⟫| := by
      rw [←abs_mul_abs_self (⟪x, y⟫)]

    rw [mul_assoc ‖⟪x, y⟫‖⁻¹ ⟪x, y⟫  ⟪x, y⟫, this, ←mul_assoc] at h_simp
    have h_abs : |⟪x, y⟫| ≠ 0 := abs_ne_zero.mpr hnxy
    have inv_mul : |⟪x, y⟫| * |⟪x, y⟫|⁻¹ = 1 := by
      exact CommGroupWithZero.mul_inv_cancel |⟪x, y⟫| hxy
    rw [Real.norm_eq_abs ⟪x, y⟫, mul_comm |⟪x, y⟫|⁻¹ |⟪x, y⟫|, inv_mul, one_mul] at h_simp

    have h_div_neg : 1 ≥ |⟪x, y⟫| * ‖y‖⁻¹ * ‖x‖⁻¹ := by linarith
    have : ‖y‖⁻¹ * ‖x‖⁻¹ = (‖y‖ * ‖x‖)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, one_div_mul_one_div, ←inv_eq_one_div]
    rw [mul_assoc, this, mul_comm] at h_div_neg

    have h_pos : 0 < ‖y‖ * ‖x‖ := non_neg
    have h_bound : (‖y‖ * ‖x‖)⁻¹ * |⟪x, y⟫| ≤ 1 := by
      rwa [ge_iff_le] at h_div_neg

    rwa [inv_mul_le_one₀ h_pos, ←Real.norm_eq_abs, mul_comm] at h_bound
