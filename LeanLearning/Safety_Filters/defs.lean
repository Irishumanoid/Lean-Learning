import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finmap

open RealInnerProductSpace

variable {n n_x n_u n_d n_h : ℕ}
notation "ℝ^{" n "}" => EuclideanSpace ℝ (Fin n)

def StateSpace := ℝ^{n_x}
def InputSpace := ℝ^{n_u}
def DistSpace := ℝ^{n_d}
def InfoState := ℝ^{n_h}
instance {n_d : ℕ} : Zero (@DistSpace n_d) := ⟨fun _ => 0⟩ -- zero element exists

-- disjoint collections of state vectors
structure FailureSet (n_x : ℕ) where
  carrier: Set (@StateSpace n_x)

structure ConstraintSet (n_x : ℕ) (failureSet : @FailureSet n_x) where
  carrier: Set (@StateSpace n_x)
  no_overlap : Disjoint carrier failureSet.carrier

structure SafeSet (n_x : ℕ) (valFunc : @StateSpace n_x → Real) where
  carrier: Set (@StateSpace n_x) := {x | valFunc x ≥ 0}

def policy := @StateSpace n_x → @InputSpace n_u

def dynamics := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @StateSpace n_x -- f
def measurement := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @InfoState n_h -- h
def cost := @StateSpace n_x → @policy n_x n_u → ℝ -- J


theorem safePolicy {n_x n_u n_d : ℕ}
  (valFunc : @StateSpace n_x → Real) (safeSet : @SafeSet n_x valFunc) (dyn : @dynamics n_x n_u n_d) (dist : DistSpace) :
  ∃ (p : policy), ∀ x ∈ safeSet.carrier, dyn x (p x) dist ∈ safeSet.carrier := sorry


def dynamicsApprox := @InfoState n_h → @InputSpace n_u → @DistSpace n_d → @StateSpace n_x

structure SafetyMonitor where
  monitor: @InfoState n_h → @InputSpace n_u → ℝ
  fallback: @InfoState n_h → @InputSpace n_u
  F_eta: Set (@InfoState n_h) -- info states with potential failure
  valFunc : @StateSpace n_x → Real
  dyn : dynamicsApprox
  safety_condition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u), monitor η u ≥ 0 →
    η ∉ F_eta ∧
    (∀ d : @DistSpace n_d,
    valFunc (dyn η (fallback η) d) ≥ 0)

structure SafetyFilter where
  fallback: @InfoState n_h → @InputSpace n_u
  safetyMonitor: @SafetyMonitor (n_x := n_x) (n_u := n_u) (n_d := n_d) (n_h := n_h)
  intervention: @InfoState n_h → @InputSpace n_u → @InputSpace n_u
  safety_condition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u),
    safetyMonitor.monitor η (fallback η) ≥ 0 → safetyMonitor.monitor η (intervention η u) ≥ 0


-- ∀ x ∈ Ω, f(x, π(x), 0) ∈ Ω
open Finset
def isControlInvariant
  [Fintype (@StateSpace n_x)] [Fintype (@DistSpace n_d)] -- enumerable to test concrete policies
  (Ω : Set (@StateSpace n_x) → Bool) (dyn : @dynamics n_x n_u n_d)
  (potential_policies : List (@StateSpace n_x → @InputSpace n_u)) : Bool :=
    potential_policies.any λ π =>
    (Finset.univ : Finset (@StateSpace n_x)).all λ x =>
    Ω x → (Finset.univ : Finset (@DistSpace n_d)).all λ d =>
    Ω (dyn x (π x)) -- does output still exist in safe set


/-
  Proposition 1 (perfect safety filter):
  ∃ filter, filter(x, s) ∈ U_safe (U_safe ⊆ U) if U_safe ≠ ∅ AND filter(x, s) = u if u ∈ U_safe
-/
structure PerfectSafetyFilter where
  filter : @StateSpace n_x → @InputSpace n_u → @InputSpace n_u
  x : @StateSpace n_x
  u : @InputSpace n_u
  U_safe : Set (@InputSpace n_u) -- keeps next system state within maximal safe set
  cost : @cost n_x n_u
  safety_condition : (Set.Nonempty U_safe → filter x u ∈ U_safe) ∧ (u ∈ U_safe → filter x u = u)

/-
  J_optimized(x_init) = min over policy_task J(x_init, policy_task)
  such that u_k = filter (x_k, policy_task(x_k))
-/
structure OptimalSafeControl where
  J : @cost n_x n_u
  x0 : @StateSpace n_x
  π_task : @policy n_x n_u
  φ : @PerfectSafetyFilter n_x n_u
  dynamics : @dynamics n_x n_u n_d
  zero_dist : @DistSpace n_d := 0

  optimality :
    ∀ (π : @policy n_x n_u),
    (∀ (x_k : @StateSpace n_x),
      let u_k := φ.filter x_k (π x_k)
      let x_next := dynamics x_k u_k 0
      J x0 π_task ≤ J x0 π -- min cost for π_task
      ∧ φ.filter x_next (π x_next) ∈ φ.U_safe)

  safety_constraint :
    ∀ (x_k : @StateSpace n_x),
    let u_k := φ.filter x_k (π_task x_k)
    φ.filter x_k u_k ∈ φ.U_safe ∧ (u_k ∈ φ.U_safe → φ.filter x_k u_k = u_k)
