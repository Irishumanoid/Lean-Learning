import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Basic

open RealInnerProductSpace

variable {n n_x n_u n_d n_h : ℕ}
notation "ℝ^{" n "}" => EuclideanSpace ℝ (Fin n)

def StateSpace := ℝ^{n_x}
def InputSpace := ℝ^{n_u}
def DistSpace := ℝ^{n_d}
def InfoState := ℝ^{n_h}
instance {n_d : ℕ} : Zero (@DistSpace n_d) := ⟨fun _ => 0⟩ -- zero element exists

def policy := @StateSpace n_x → @InputSpace n_u
def dynamics := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @StateSpace n_x -- f
def measurement := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @InfoState n_h -- h
def cost := @StateSpace n_x → @policy n_x n_u → ℝ -- J


structure FailureSet (n_x : ℕ) where
  carrier: Set (@StateSpace n_x)

structure ConstraintSet (n_x : ℕ) (failureSet : @FailureSet n_x) where
  carrier: Set (@StateSpace n_x)
  no_overlap : Disjoint carrier failureSet.carrier

def safetyValueFunction := @StateSpace n_x → Real
def isSafeSet (s : safetyValueFunction) (Ω : Set (@StateSpace n_x)) := ∀ x ∈ Ω, s x ≥ 0

structure SafeSet (s : safetyValueFunction) where
  carrier: Set (@StateSpace n_x)
  safetyCondition: isSafeSet s carrier

def maxSafeSet (s : @safetyValueFunction n_x) : SafeSet s := {
  carrier := {x | s x ≥ 0}
  safetyCondition := by
    intro x hx
    exact hx
}

def safeSubsetMax (s : @safetyValueFunction n_x) (safeSet : SafeSet s) :
  safeSet.carrier ⊆ (maxSafeSet s).carrier := by
    intro x hx
    have : s x ≥ 0 := safeSet.safetyCondition x hx
    exact this


structure SafePolicy where
  safetyValFunc : @StateSpace n_x → Real
  safeSet : @SafeSet n_x safetyValFunc
  dyn : @dynamics n_x n_u n_d
  dist : @DistSpace n_d
  invariance: ∃ (p : policy), ∀ x ∈ safeSet.carrier, dyn x (p x) dist ∈ safeSet.carrier

def dynamicsApprox := @InfoState n_h → @InputSpace n_u → @DistSpace n_d → @StateSpace n_x

structure SafetyMonitor where
  monitor: @InfoState n_h → @InputSpace n_u → ℝ
  fallback: @InfoState n_h → @InputSpace n_u
  F_eta: Set (@InfoState n_h) -- info states with potential failure
  safetyValFunc : @StateSpace n_x → Real
  dyn : dynamicsApprox
  safety_condition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u), monitor η u ≥ 0 →
    η ∉ F_eta ∧
    (∀ d : @DistSpace n_d,
    safetyValFunc (dyn η (fallback η) d) ≥ 0)

structure SafetyFilter where
  fallback: @InfoState n_h → @InputSpace n_u
  safetyMonitor: @SafetyMonitor (n_x := n_x) (n_u := n_u) (n_d := n_d) (n_h := n_h)
  intervention: @InfoState n_h → @InputSpace n_u → @InputSpace n_u
  safety_condition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u),
    safetyMonitor.monitor η (fallback η) ≥ 0 → safetyMonitor.monitor η (intervention η u) ≥ 0


-- keeps next system state within maximal safe set (use this version instead)
def U_Safe (x : @StateSpace n_x) (dyn : @dynamics n_x n_u n_d) (s : @safetyValueFunction n_x)
  : Set (@InputSpace n_u) :=
    {u | dyn x u 0 ∈ (maxSafeSet s).carrier}

/-
  Proposition 1 (perfect safety filter):
  ∃ filter, filter(x, s) ∈ U_safe (U_safe ⊆ U) if U_safe ≠ ∅ AND filter(x, s) = u if u ∈ U_safe
-/
theorem PerfectSafetyFilter
  (filter : @StateSpace n_x → @InputSpace n_u → @InputSpace n_u)
  (x : @StateSpace n_x)
  (u : @InputSpace n_u)
  (U_safe : @StateSpace n_x → Set (@InputSpace n_u)):
  (Set.Nonempty (U_safe x) → filter x u ∈ (U_safe x)) ∧ (u ∈ (U_safe x) → filter x u = u) := by sorry



/-
  J_optimized(x_init) = min over policy_task J(x_init, policy_task)
  such that u_k = filter (x_k, policy_task(x_k))
-/
theorem OptimalSafeControl
  (J : @cost n_x n_u)
  (x0 : @StateSpace n_x)
  (π_task : @policy n_x n_u)
  (filter : @StateSpace n_x → @InputSpace n_u → @InputSpace n_u)
  (U_safe : Set (@InputSpace n_u))
  (dynamics : @dynamics n_x n_u n_d)
  (zero_dist : @DistSpace n_d := 0) :
    ∀ (π : @policy n_x n_u), (∀ (x_k : @StateSpace n_x),
      let u_k := filter x_k (π x_k); let x_next := dynamics x_k u_k 0
      J x0 π_task ≤ J x0 π -- min cost for π_task
      ∧ filter x_next (π x_next) ∈ U_safe)
    →
    ∀ (x_k : @StateSpace n_x), let u_k := filter x_k (π_task x_k)
    filter x_k u_k ∈ U_safe ∧ (u_k ∈ U_safe → filter x_k u_k = u_k) := by sorry
