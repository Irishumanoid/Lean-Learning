import LeanLearning.Safety_Filters.Base_Definitions
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

variable {n n_x n_u n_d n_h : ℕ}


structure MarginFunction where
  func:  ℝ^{n_x} → ℝ
  lipschitz: ∃ (k : NNReal), LipschitzWith k func

noncomputable
def FiniteLRValue {H : ℕ} (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) (k : Fin (H + 1)) (x : ℝ^{n_x}) :=
  let motive : (Fin (H + 1)) → Type := λ _ => ℝ^{n_x} → ℝ -- recursively defines function
  let base : motive (Fin.last H) := λ x => mf.func x
  let cast : (i : Fin H) → motive (i.succ) → motive (i.castSucc) :=
    λ _ Vk_succ =>
    min (λ x => mf.func x) (λ x => ⨅ (u : InputSpace), (⨆ (d : DistSpace), (Vk_succ (dyn x u d))))

  Fin.reverseInduction (motive := motive) base cast k x

open Topology


-- need to make decidable
noncomputable
def InfLRValue (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x) (x : ℝ^{n_x}) :=
  let valFunc := FiniteLRValue dyn mf
  λ x =>
    if h : ∃ V, Filter.Tendsto (λ H => @valFunc H 0) Filter.atTop (𝓝 V) then
      h.choose x
    else
      0


noncomputable
def lrSafetyValue (H : ℕ) (dyn : @dynamics n_x n_u n_d) (mf : @MarginFunction n_x)
    (lr_func : ∀ (k : Fin (H + 1)) (x : ℝ^{n_x}), f : InfLRValue dyn mf k x) : @safetyValueFunction n_x :=
  λ x => f dyn (lr_func 0 x)

def LRMaxSafeSet (s : @lrSafetyValue n_x) := @maxSafeSet n_x s


--- argmax thing: have some h : ∃u : U, u = ⊔ u, V_k(f(x,u,d)) ∈ U
