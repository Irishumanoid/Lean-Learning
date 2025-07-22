import Mathlib

namespace MatrixAnalysis

def Poly (R : Type*) [Ring R] (n:ℕ) := (Fin n) → R

namespace Poly

def apply
 {n:ℕ} {R S : Type*} [Ring R] [Ring S] [HMul R S S] (p : Poly R n) (x : S) : S
 := ∑ k : (Fin n) , (p k) * (x^k.val)

end Poly

namespace Example

  def q : Poly Int 3 := ![1,2,3]
  #eval q.apply 4

end Example

/- To compute simple examples that might be found in a textbook, it would be nice to automatically expand polynomial applications (which are sums) to the explicit terms of which they are composed. Mathlib has a number of finite sum theorems for this which we package into a tactic. -/

/--
`small_poly p` attempts to simplify the current goal using Poly.apply, p, and sum_univ_* for * = one, ..., eight.
-/
syntax "small_poly " ident : tactic

macro_rules
  | `(tactic | small_poly $p) =>
    `(tactic | simp[Poly.apply,
                    $p:ident,
                    Fin.sum_univ_one,
                    Fin.sum_univ_two,
                    Fin.sum_univ_three,
                    Fin.sum_univ_four,
                    Fin.sum_univ_five,
                    Fin.sum_univ_six,
                    Fin.sum_univ_seven,
                    Fin.sum_univ_eight])


end MatrixAnalysis
