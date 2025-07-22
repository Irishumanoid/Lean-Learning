import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

variable {n : ℕ} (x y : Fin n → ℝ)

theorem cauchy_schwarz_concrete : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  exact abs_inner_le_norm x y

theorem inner_prod_over_mag (h : x ≠ 0) : ⟪x, x⟫ / ‖x‖^2 = 1 := by
  rw [norm_eq_sqrt_inner, sq_sqrt (inner_self_nonneg)]
  exact div_self (inner_self_ne_zero.mpr h)

theorem cauchy_schwarz (h : ⟪x, y⟫ ≠ 0) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  let α = ⟪x, y⟫ / ‖⟪x, y⟫‖
  have ha : 0 ≤ ⟪x/‖x‖ - α • y/‖y‖, x/‖x‖ - α • y/‖y‖⟫ := nonneg_re
  have h0 : α * α = 1 := inner_prod_over_mag
  rw [inner_add_left] at ha
  repeat rw [inner_add_right, inner_smul_left, inner_smul_right, simp] at ha
  simp [h0] at ha
  nth_rewrite 3 [real_inner_comm] at ha
  repeat rw [inner_prod_over_mag] at ha
  sorry
