import LeanLearning.Safety_Filters.Base_Definitions
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

variable {n n_u n_d n_h : ℕ}
variable {𝓗 : Type} [PseudoEMetricSpace 𝓗]

open scoped Classical

def ValueFunction := 𝓗 → ℝ

structure MarginFunction (𝓗 : Type) [PseudoEMetricSpace 𝓗] where
  toFun: 𝓗 → ℝ
  lipschitz: ∃ (k : NNReal), LipschitzWith k toFun

instance : CoeFun (MarginFunction 𝓗) (λ _ => 𝓗 → ℝ) where
  coe f := f.toFun

noncomputable
def FiniteTimeValueFunction {H : ℕ} (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) (k : Fin (H + 1)) (η : 𝓗) : ℝ :=
  let motive (𝓗 : Type) : (Fin (H + 1)) → Type := λ _ => 𝓗 → ℝ -- recursively defines functions
  let base : motive 𝓗 (Fin.last H) := λ x => mf x
  let cast : (i : Fin H) → motive 𝓗 (i.succ) → motive 𝓗 (i.castSucc) :=
    λ _ Vk_succ =>
    min (λ x => mf x) (λ x => ⨅ (u : ℝ^{n_u}), (⨆ (d : ℝ^{n_d}), (Vk_succ (dyn x u d))))

  Fin.reverseInduction base cast k η

noncomputable
def InfiniteTimeValueFunction (f : @dynamics n_u n_d 𝓗) (margin : MarginFunction 𝓗) : @ValueFunction 𝓗 :=
  if h : ∃ V : ValueFunction, ∀ x : 𝓗, V x = min (margin x) (⨅ (u : ℝ^{n_u}), (⨆ (d : ℝ^{n_d}), (V (f x u d)))) then
    Classical.choose h
  else
    λ _ => 0

noncomputable
def lrSafetyValue (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) : @ValueFunction 𝓗 :=
  λ x => InfiniteTimeValueFunction dyn mf x

noncomputable
def lrMaxSafeSet (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) :=
  maxSafeSet (@lrSafetyValue n_u n_d 𝓗 _ dyn mf)


-- π*(x)
noncomputable
def lrOptimalPolicy (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) (x : 𝓗) : ℝ^{n_u} :=
  Classical.choose (by
      have : ∃ (u : ℝ^{n_u}), ⨅ (d : ℝ^{n_d}), InfiniteTimeValueFunction dyn mf (dyn x u d) =
              ⨆ (u' : ℝ^{n_u}), ⨅ (d : ℝ^{n_d}), InfiniteTimeValueFunction dyn mf (dyn x u' d) := by
        -- prove the supremum is attained over ℝ^{n_u} (state compactness and continuity?)
        sorry
      exact this)


noncomputable
def lrSafetyMonitor (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) (f_eta : FailureSet (lrSafetyValue dyn mf)):
    @SafetyMonitor n_u n_d 𝓗 (lrSafetyValue dyn mf) dyn f_eta := {
  monitor := by
    intro η u
    let x := dyn η u 0
    exact InfiniteTimeValueFunction dyn mf x
  fallback := by
    intro η
    have safeSet : Set ℝ^{n_u} := (U_safe η dyn (lrSafetyValue dyn mf))

    by_cases h : safeSet.Nonempty
      . exact h.choose
      . exact 0

  safetyCondition := sorry
}

noncomputable
def lrSafetyFilter (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) (f_eta : FailureSet (lrSafetyValue dyn mf)):
  @SafetyFilter n_u n_d 𝓗 (lrSafetyValue dyn mf) dyn f_eta := {
  fallback := sorry
  safetyMonitor := @lrSafetyMonitor n_u n_d 𝓗 _ dyn mf f_eta
  intervention := sorry
  safetyCondition := sorry
  interventionProp := sorry
}

noncomputable
def safetyFilterEval (η : 𝓗) (dyn : @dynamics n_u n_d 𝓗) (mf : MarginFunction 𝓗) (π_task : 𝓗 → ℝ^{n_u}) : ℝ^{n_u} :=
  if ⨅ (d : ℝ^{n_d}), InfiniteTimeValueFunction dyn mf (dyn η (π_task η) d) ≥ 0 then
    π_task η
  else
    lrOptimalPolicy dyn mf η
