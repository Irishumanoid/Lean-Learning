import Mathlib

namespace MatrixAnalysis

def row_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k: (Fin m))
    : Matrix (Fin (m-1)) (Fin n) ℂ :=
    Matrix.of λ i j =>
      if (Fin.mk i (Nat.lt_of_lt_pred i.isLt)) < k
      then A (Fin.mk i (Nat.lt_of_lt_pred i.isLt)) j
      else A (Fin.mk (i+1) (Nat.add_lt_of_lt_sub i.isLt)) j

def col_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k: (Fin n))
    : Matrix (Fin m) (Fin (n-1)) ℂ :=
    Matrix.of λ i j =>
      if (Fin.mk j (Nat.lt_of_lt_pred j.isLt)) < k
      then A i (Fin.mk j (Nat.lt_of_lt_pred j.isLt))
      else A i (Fin.mk (j+1) (Nat.add_lt_of_lt_sub j.isLt))

def row_col_minor
    {n m: ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : (Fin m)) (j : (Fin n))
    : Matrix (Fin (m-1)) (Fin (n-1)) ℂ :=
    row_minor (col_minor A j) i

def A : Matrix (Fin 3) (Fin 3) ℂ := !![1,0,2;0,3,0;4,0,5]

#eval row_minor A 1
#eval row_minor A 2
#eval row_col_minor A 1 1

def q : (Fin 5) := 3

variable (e : (Fin 4) ≃ (Fin 4))
#check e 1

#eval (-1)^3

def s {n:ℕ} (k : Fin n) := if Odd k.val then -1 else 1

noncomputable
def det {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :=
  match n with
  | Nat.zero => 1
  | Nat.succ _ => ∑ j, (s j) • ((A 0 j) * det (row_col_minor A 0 j))

theorem our_det_is_their_det {n:ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
  : det A = Matrix.det A := by
  sorry

theorem det_combo {n:ℕ} {hnp : n > 0} (A : Matrix (Fin n) (Fin n) ℂ)
  : ∃ v : Matrix (Fin n) (Fin 1) ℂ, det A = ∑ i, (A ⟨ 0, hnp ⟩ i) * (v i 0) := by
  sorry

/- This version of the theorem basically just wraps around Mathlib's -/
theorem det_mult'
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
  : Matrix.det (A*B) = (Matrix.det A) * (Matrix.det B) := by
  exact Matrix.det_mul A B

theorem det_mult
  {n:ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
  : det (A*B) = (det A) * (det B) := by
  sorry
