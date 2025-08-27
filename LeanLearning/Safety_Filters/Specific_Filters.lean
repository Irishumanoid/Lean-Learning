import LeanLearning.Safety_Filters.Base_Definitions
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

variable {n n_x n_u n_d n_h : ℕ}


structure MarginFunction where
  func:  ℝ^{n_x} → ℝ
  lipschitz: ∃ (k : NNReal), LipschitzWith k func

noncomputable
def FiniteLRValue {H : ℕ} (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) (k : Fin (H + 1)) (x : ℝ^{n_x}) : ℝ :=
  let motive : (Fin (H + 1)) → Type := λ _ => ℝ^{n_x} → ℝ -- recursively defines functions
  let base : motive (Fin.last H) := λ x => mf.func x
  let cast : (i : Fin H) → motive (i.succ) → motive (i.castSucc) :=
    λ _ Vk_succ =>
    min (λ x => mf.func x) (λ x => ⨅ (u : InputSpace), (⨆ (d : DistSpace), (Vk_succ (dyn x u d))))

  Fin.reverseInduction (motive := motive) base cast k x

noncomputable
def InfLRValue (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) (x : ℝ^{n_x}) : ℝ :=
  -- limit as h → ∞ for last value in Fin h AKA limsup_{H → ∞} V_H(H, x)
  Filter.limsup (λ (h : ℕ) => FiniteLRValue dyn mf (Fin.last h) x) Filter.atTop

noncomputable
def lrSafetyValue (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) : @safetyValueFunction n_x :=
  λ x => InfLRValue dyn mf x

noncomputable
def lrMaxSafeSet (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) :=
  @maxSafeSet n_x (lrSafetyValue dyn mf)


-- π*(x)
noncomputable
def lrOptimalPolicy (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) (x : @StateSpace n_x) : @InputSpace n_u :=
  Classical.choose (by
      have : ∃ (u : InputSpace), ⨅ (d : DistSpace), InfLRValue dyn mf (dyn x u d) =
              ⨆ (u' : InputSpace), ⨅ (d : DistSpace), InfLRValue dyn mf (dyn x u' d) := by
        -- prove the supremum is attained over InputSpace (state compactness and continuity?)
        sorry
      exact this)


-- define safety monitor and safety filter, then define switch-type intervention for safety filter
  --let safetyValFunc := lrSafetyValue dyn mf
  --let maxSafe := {u | ∀ d : @DistSpace n_d, dynApprox xh u d ∈ (maxSafeSet safetyValFunc).carrier}
noncomputable
def lrSafetyMonitor (dyn : @dynamics n_x n_u n_d) (dynApprox : @dynamicsApprox n_x n_u n_d n_h) (mf : @MarginFunction n_x) :
    @SafetyMonitor n_x n_u n_d n_h (lrSafetyValue dyn mf) dyn dynApprox := {
  monitor := by
    intro η u
    let x := dynApprox η u 0
    exact InfLRValue dyn mf x
  fallback := by
    intro η
    sorry
  safetyCondition := sorry
  observableSafetyCondition := by
    intro η u x d monitor
    dsimp at monitor
    unfold lrSafetyValue
    sorry
}

noncomputable
def lrSafetyFilter (dyn : @dynamics n_x n_u n_d) (dynApprox : @dynamicsApprox n_x n_u n_d n_h) (mf : @MarginFunction n_x) :
  @SafetyFilter n_x n_u n_d n_h (lrSafetyValue dyn mf) dyn dynApprox := {
  fallback := sorry
  safetyMonitor := sorry
  intervention := sorry
  safetyCondition := sorry
  interventionProp := sorry
}

noncomputable
def safetyFilterEval (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x)
  (x : @StateSpace n_x) (π_task : @policy n_x n_u) : @InputSpace n_u :=
  if ⨅ (d : DistSpace), InfLRValue dyn mf (dyn x (π_task x) d) ≥ 0 then
    π_task x
  else
    lrOptimalPolicy dyn mf x
