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
  have xnorm_mul_ynorm_nonneg : ‖x‖ * ‖y‖ ≥ 0 :=
    by refine Left.mul_nonneg ?_ ?_
       <;> apply norm_nonneg

  by_cases hxy : ‖⟪x, y⟫‖ = 0
  . rw [hxy]
    exact xnorm_mul_ynorm_nonneg

  . let α := ⟪x, y⟫ / ‖⟪x, y⟫‖
    have h_inner_prod_nonzero : ⟪x, y⟫ ≠ 0 := by exact abs_ne_zero.mp hxy
    have h_inners_nonzero : ⟪x, x⟫ ≠ 0 ∧ ⟪y, y⟫ ≠ 0 := nonzero_inner_implies_nonzero_vectors x y h_inner_prod_nonzero
    have h_sq_eq_one : α ^ 2 = 1 := Eq.trans (pow_two α) (inner_prod_over_mag ⟪x, y⟫ h_inner_prod_nonzero)
    obtain ⟨hnx, hny⟩ : ‖x‖ > 0 ∧ ‖y‖ > 0 := by exact nonzero_inner_implies_nonzero_mag h_inner_prod_nonzero

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
          [inv_eq_one_div ‖x‖, inv_eq_one_div ‖y‖,
          simp_mul_with_coeff α y y_mag_ne_zero]
              ring_nf

      _ = 1 - α * (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ - α * (1 / ‖y‖) * (1 / ‖x‖) * ⟪x, y⟫ + 1
        := by rw
          [h_sq_eq_one, smul_eq_mul, get_one x h_inners_nonzero.left,
          one_mul, get_one y h_inners_nonzero.right]

      _ = 2 - 2 * α * ‖x‖⁻¹ * ‖y‖⁻¹ * ⟪x, y⟫
        := by field_simp only [hnx, hny]
              ring_nf

    have : 1 ≥ α * ‖x‖⁻¹ * ‖y‖⁻¹ * ⟪x, y⟫ := by linarith

    calc
      ‖x‖ * ‖y‖ ≥ α * ⟪x, y⟫
                := by convert (mul_le_mul_of_nonneg_left this xnorm_mul_ynorm_nonneg).ge using 1
                      . rw [mul_one]
                      . field_simp

              _ = ⟪x, y⟫^2 / ‖⟪x, y⟫‖
                := by simp only [α]
                      ring_nf

              _ = |⟪x, y⟫|^2 / |⟪x, y⟫|
                := by simp [sq_abs ⟪x, y⟫]

              _ = |⟪x, y⟫|
                := by field_simp only [h_inner_prod_nonzero]
                      ring_nf

theorem triangle_inequality : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  suffices ‖x + y‖^2 ≤ (‖x‖ + ‖y‖)^2 by
    convert Real.sqrt_le_sqrt this using 1
    <;> field_simp

  rw [←real_inner_self_eq_norm_sq, real_inner_add_add_self]
  ring_nf
  nth_rewrite 4 [add_comm]

  repeat rw [real_inner_self_eq_norm_sq]
  ac_change ‖x‖ ^ 2 + (⟪x, y⟫ * 2 + ‖y‖ ^ 2) ≤ ‖x‖ ^ 2 + (‖x‖ * ‖y‖ * 2 + ‖y‖ ^ 2)
  gcongr
  have h_abs := cauchy_schwarz (x := x) (y := y)
  have : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := (abs_le.mp h_abs).right
  linarith
