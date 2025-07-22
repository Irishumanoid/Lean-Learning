import Mathlib
import Mathlib.Analysis.InnerProductSpace.Basic

-- size n vector of type α
notation α "^{" n "}" => Fin n → α
notation α "^{" m","n "}" => Matrix (Fin m) (Fin n) α
notation α "^{" n"²" "}" => Matrix (Fin n) (Fin n) α

theorem matrix_eq_all {n m: ℕ} {A B : ℂ^{m,n}}
  : A = B ↔ ∀ i j, A i j = B i j := by
  constructor
  . intro h i j
    exact congrFun (congrFun h i) j
  . exact Matrix.ext

theorem matrix_neq_exists {n m : ℕ} {A B : ℂ^{n,m}}
  : A ≠ B ↔ ∃ i j, A i j ≠ B i j := by
  simp[matrix_eq_all]


def vec_prod {n} (a b : Fin n → ℂ) : Fin n → ℂ := λ i => a i * b i
infixl:70 " ⊙ " => vec_prod
variable {n : ℕ} (a b : Fin n → ℂ)
#check a ⊙ b

noncomputable
def vec_mag {n} (a : Fin n → ℂ) : ℝ := ‖a‖

theorem cauchy_schwarz_inequality {n : ℕ} {u v : ℂ^{n}} : vec_mag (u ⊙ v) ≤ ‖u‖ * ‖v‖ :=
  let c : ℂ := vec_mag (u ⊙ v) / vec_mag (v ⊙ v)
  let ucv := u - c • v
  have hucv : 0 ≤ ‖ucv‖ := norm_nonneg ucv
  sorry
