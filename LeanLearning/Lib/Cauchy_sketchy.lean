import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

open RealInnerProductSpace

notation "ℝ^{" n "}" => EuclideanSpace ℝ (Fin n)
variable {n : ℕ} (a : ℝ) (x y : ℝ^{n})

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
  rwa [one_div_mul_one_div, norm_eq_sqrt_real_inner, ←pow_two,
      Real.sq_sqrt (real_inner_self_nonneg), mul_comm, mul_one_div, div_self]


lemma nonzero_inner_implies_nonzero_vectors
  (h : ⟪x, y⟫ ≠ 0) : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := by
  constructor <;> (
    intro hx
    have := inner_self_eq_zero.mp hx
    simp [this] at h)

lemma nonzero_inner_implies_nonzero_mag {x y : ℝ^{n}} (h : ⟪x, y⟫ ≠ 0) : ‖x‖ > 0 ∧ ‖y‖ > 0 := by
  constructor <;> (
  · refine norm_pos_iff.mpr ?_
    intro hx
    simp [hx] at h
    )


theorem cauchy_schwarz : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  by_cases hxy : ‖⟪x, y⟫‖ = 0
  . rw [hxy]
    refine Left.mul_nonneg ?_ ?_
      <;> apply norm_nonneg

  . let α := ⟪x, y⟫ / ‖⟪x, y⟫‖

    have ha : 0 ≤ ⟪‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y, ‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y⟫ := real_inner_self_nonneg
    rw [inner_sub_sub_self] at ha
    simp only [real_inner_smul_left, real_inner_smul_right] at ha
    rw [real_inner_comm x y] at ha
    repeat rw [← mul_assoc] at ha
    rw [mul_comm ‖x‖⁻¹ (α • ‖y‖⁻¹)] at ha

    let xy_inner : ℝ := ⟪x, y⟫
    have h_inner_prod_nonzero : xy_inner ≠ 0 := by exact abs_ne_zero.mp hxy
    have h_sq_eq_one : α ^ 2 = 1 := Eq.trans (pow_two α) (inner_prod_over_mag xy_inner h_inner_prod_nonzero)

    have h_inners_nonzero : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := nonzero_inner_implies_nonzero_vectors x y h_inner_prod_nonzero
    have h_mags_nonzero : ‖x‖ > 0 ∧ ‖y‖ > 0 := nonzero_inner_implies_nonzero_mag h_inner_prod_nonzero
    have : 1 / ‖y‖ ^ 2 = 1 / ‖y‖ * (1 / ‖y‖) := by rw [one_div_mul_one_div, pow_two]

    have hny : ‖y‖ > 0 := h_mags_nonzero.right
    have y_mag_ne_zero : ‖y‖ ≠ 0 := by
      rw [gt_iff_lt] at hny
      exact Ne.symm (ne_of_lt hny)

    rw [inv_eq_one_div ‖x‖, inv_eq_one_div ‖y‖, simp_mul_with_coeff α y y_mag_ne_zero] at ha
    rw [h_sq_eq_one, one_mul, smul_eq_mul, this] at ha
    rw [get_one x h_inners_nonzero.left, get_one y h_inners_nonzero.right] at ha

    field_simp only [h_mags_nonzero.left, h_mags_nonzero.right, mul_one] at ha
    ring_nf at ha

    have h_div: 0 ≤ (2 - α * ⟪x, y⟫ * ‖y‖⁻¹ * ‖x‖⁻¹ * 2) / 2 :=
      div_nonneg ha zero_le_two
    have h_simp : 0 ≤ 1 - ⟪x, y⟫ / ‖⟪x, y⟫‖ * ⟪x, y⟫ * ‖y‖⁻¹ * ‖x‖⁻¹ := by
      rwa [sub_div, mul_div_assoc, div_self (two_ne_zero), mul_one] at h_div
    rw [div_eq_inv_mul] at h_simp
    have : ⟪x, y⟫ * ⟪x, y⟫ = |⟪x, y⟫| * |⟪x, y⟫| := by
      rw [←abs_mul_abs_self (⟪x, y⟫)]

    rw [mul_assoc ‖⟪x, y⟫‖⁻¹ ⟪x, y⟫  ⟪x, y⟫, this, ←mul_assoc] at h_simp
    have inv_mul : |⟪x, y⟫| * |⟪x, y⟫|⁻¹ = 1 := by
      exact CommGroupWithZero.mul_inv_cancel |⟪x, y⟫| hxy
    rw [Real.norm_eq_abs ⟪x, y⟫, mul_comm |⟪x, y⟫|⁻¹ |⟪x, y⟫|, inv_mul, one_mul] at h_simp

    have h_div_neg : 1 ≥ |⟪x, y⟫| * ‖y‖⁻¹ * ‖x‖⁻¹ := by linarith
    have : ‖y‖⁻¹ * ‖x‖⁻¹ = (‖y‖ * ‖x‖)⁻¹ := by field_simp
    rw [mul_assoc, this, mul_comm] at h_div_neg

    have non_neg : ‖y‖ * ‖x‖ > 0 := by apply Left.mul_pos h_mags_nonzero.right h_mags_nonzero.left
    have h_pos : 0 < ‖y‖ * ‖x‖ := non_neg
    have h_bound : (‖y‖ * ‖x‖)⁻¹ * |⟪x, y⟫| ≤ 1 := by
      rwa [ge_iff_le] at h_div_neg
    rwa [inv_mul_le_one₀ h_pos, ←Real.norm_eq_abs, mul_comm] at h_bound


theorem cauchy_schwarz_clean : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have xnorm_mul_ynorm_nonneg : ‖x‖ * ‖y‖ ≥ 0 :=
    by refine Left.mul_nonneg ?_ ?_
       <;> apply norm_nonneg

  by_cases hxy : ‖⟪x, y⟫‖ = 0
  . rw [hxy]
    exact xnorm_mul_ynorm_nonneg

  . let α := ⟪x, y⟫ / ‖⟪x, y⟫‖
    have h_inner_prod_nonzero : ⟪x, y⟫ ≠ 0 := by exact abs_ne_zero.mp hxy
    have h_inners_nonzero : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := nonzero_inner_implies_nonzero_vectors x y h_inner_prod_nonzero
    have h_mags_nonzero : ‖x‖ > 0 ∧ ‖y‖ > 0 := nonzero_inner_implies_nonzero_mag h_inner_prod_nonzero
    have h_sq_eq_one : α ^ 2 = 1 := Eq.trans (pow_two α) (inner_prod_over_mag ⟪x, y⟫ h_inner_prod_nonzero)

    have hny : ‖y‖ > 0 := h_mags_nonzero.right
    have y_mag_ne_zero : ‖y‖ ≠ 0 := by
      rw [gt_iff_lt] at hny
      exact Ne.symm (ne_of_lt hny)

    have : 0 ≤ 2 - 2 * α * ‖x‖⁻¹ * ‖y‖⁻¹ *  ⟪x, y⟫ := by calc
      0 ≤ ⟪‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y, ‖x‖⁻¹ • x  - (α • ‖y‖⁻¹) • y⟫
        := real_inner_self_nonneg

      _ = ⟪‖x‖⁻¹ • x, ‖x‖⁻¹ • x⟫ - ⟪‖x‖⁻¹ • x, (α • ‖y‖⁻¹) • y⟫ - ⟪(α • ‖y‖⁻¹) • y, ‖x‖⁻¹ • x⟫ +
          ⟪(α • ‖y‖⁻¹) • y, (α • ‖y‖⁻¹) • y⟫
        := by rw [inner_sub_sub_self]

      _ = ‖x‖⁻¹ * ‖x‖⁻¹ * ⟪x, x⟫ - α • ‖y‖⁻¹ * (‖x‖⁻¹ * ⟪x, y⟫) - ‖x‖⁻¹ * (α • ‖y‖⁻¹ * ⟪x, y⟫) +
          α • ‖y‖⁻¹ * (α • ‖y‖⁻¹ * ⟪y, y⟫)
        := by simp only [real_inner_smul_left, real_inner_smul_right]
              rw [real_inner_comm x y]
              ring

      _ = ‖x‖⁻¹ * ‖x‖⁻¹ * ⟪x, x⟫ - α • ‖y‖⁻¹ * ‖x‖⁻¹ * ⟪x, y⟫ - α • ‖y‖⁻¹ * ‖x‖⁻¹ * ⟪x, y⟫ +
          α • ‖y‖⁻¹ * α • ‖y‖⁻¹ * ⟪y, y⟫
        := by ring_nf

      _ =  1 / ‖x‖ * (1 / ‖x‖) * ⟪x, x⟫ - α • (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ - α • (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ +
          α ^ 2 * 1 / ‖y‖ * (1 / ‖y‖) * ⟪y, y⟫
        := by rw
          [inv_eq_one_div ‖x‖,
          inv_eq_one_div ‖y‖,
          simp_mul_with_coeff α y y_mag_ne_zero]
              ring_nf

      _ = 1 - α * (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ - α * (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ + 1
        := by rw
          [h_sq_eq_one, smul_eq_mul, get_one x h_inners_nonzero.left,
          one_mul, get_one y h_inners_nonzero.right]

      _ = 2 - 2 * α * ‖x‖⁻¹ * ‖y‖⁻¹ * ⟪x, y⟫
        := by field_simp only [h_mags_nonzero.left, h_mags_nonzero.right]
              ring_nf

    have h_div_neg : 1 ≥ ‖x‖⁻¹ * ‖y‖⁻¹ * ⟪x, y⟫ * α := by linarith
    simp only [α] at h_div_neg
    have : ‖x‖⁻¹ * ‖y‖⁻¹ = (‖y‖ * ‖x‖)⁻¹ := by
      field_simp
      rw [mul_comm]
    rw [mul_assoc, this, ←mul_div_assoc, ←abs_mul_abs_self (⟪x, y⟫), ←Real.norm_eq_abs] at h_div_neg
    have : (‖y‖ * ‖x‖)⁻¹ * (‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ / ‖⟪x, y⟫‖) = (‖y‖ * ‖x‖)⁻¹ * |⟪x, y⟫| := sorry
    rw [this] at h_div_neg

    have non_neg : ‖y‖ * ‖x‖ > 0 := by apply Left.mul_pos h_mags_nonzero.right h_mags_nonzero.left
    have h_pos : 0 < ‖y‖ * ‖x‖ := non_neg
    have h_bound : (‖y‖ * ‖x‖)⁻¹ * |⟪x, y⟫| ≤ 1 := by
      rw [ge_iff_le] at h_div_neg
    rwa [inv_mul_le_one₀ h_pos, mul_comm] at h_bound
