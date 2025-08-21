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
def cost := @StateSpace n_x → @policy n_x n_u → ℝ


def safetyValueFunction := @StateSpace n_x → ℝ
def isSafeSet (s : safetyValueFunction) (Ω : Set (@StateSpace n_x)) := ∀ x ∈ Ω, s x ≥ 0

structure FailureSet (s : @safetyValueFunction n_x) where
  carrier: Set (@StateSpace n_x)
  isFailureSet: carrier = {x | s x < 0}

structure ConstraintSet (s : safetyValueFunction) (failureSet : @FailureSet n_x s) where
  carrier: Set (@StateSpace n_x)
  no_overlap : Disjoint carrier failureSet.carrier

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

structure SafetyMonitor (safetyValFunc : @StateSpace n_x → ℝ) (dynComplete : @dynamics n_x n_u n_d) where
  monitor: @InfoState n_h → @InputSpace n_u → ℝ
  fallback: @InfoState n_h → @InputSpace n_u
  F_eta: Set (@InfoState n_h) -- info states with potential failure
  dyn : dynamicsApprox
  safetyCondition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u), monitor η u ≥ 0 →
    η ∉ F_eta ∧
    (∀ d : @DistSpace n_d,
    safetyValFunc (dyn η (fallback η) d) ≥ 0)
  observableSafetyCondition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u) (x : @StateSpace n_x) (d : @DistSpace n_d),
    monitor η u ≥ 0 → safetyValFunc (dynComplete x u d) ≥ 0


structure SafetyFilter (safetyValFunc : @StateSpace n_x → ℝ) (dyn : @dynamics n_x n_u n_d) where
  fallback: @InfoState n_h → @InputSpace n_u
  safetyMonitor: @SafetyMonitor safetyValFunc dyn (n_x := n_x) (n_u := n_u) (n_d := n_d) (n_h := n_h)
  intervention: @InfoState n_h → @InputSpace n_u → @InputSpace n_u
  safetyCondition:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u),
    safetyMonitor.monitor η (fallback η) ≥ 0 → safetyMonitor.monitor η (intervention η u) ≥ 0
  interventionProp:
    ∀ (η : @InfoState n_h) (u : @InputSpace n_u),
    safetyMonitor.monitor η (intervention η u) ≥ 0 → safetyMonitor.monitor η u ≥ 0


-- keeps next system state within maximal safe set
def U_safe (x : @StateSpace n_x) (dyn : @dynamics n_x n_u n_d) (s : @safetyValueFunction n_x)
  : Set (@InputSpace n_u) :=
    {u | ∀ d : @DistSpace n_d, dyn x u d ∈ (maxSafeSet s).carrier}

/-
  Proposition 1 (perfect safety filter):
  ∃ filter, filter(x, s) ∈ U_safe (U_safe ⊆ U) if U_safe ≠ ∅ AND filter(x, s) = u if u ∈ U_safe
-/
noncomputable
def safetyFilter (dyn : @dynamics n_x n_u n_d) (s : @safetyValueFunction n_x) :
  @StateSpace n_x → @InputSpace n_u → @InputSpace n_u := by
  intro x u
  by_cases h : u ∈ U_safe x dyn s
  . exact u
  . by_cases h_nonempty : (U_safe x dyn s).Nonempty
    . exact h_nonempty.choose
    . exact u

theorem perfectSafetyFilter
  (dyn : @dynamics n_x n_u n_d)
  (s : @safetyValueFunction n_x):
  ∃ filter : @StateSpace n_x → @InputSpace n_u → @InputSpace n_u,
  ∀ (x : @StateSpace n_x) (u : @InputSpace n_u),
  ((U_safe x dyn s).Nonempty → filter x u ∈ (U_safe x dyn s)) ∧ (u ∈ (U_safe x dyn s) → filter x u = u) := by
    refine ⟨safetyFilter dyn s, ?_⟩
    intro x u
    constructor
    . intro h_nonempty
      unfold safetyFilter
      by_cases h_safe : u ∈ U_safe x dyn s
        -- if else branches of filter definition
      . rw [dif_pos h_safe]; exact h_safe
      . rw [dif_neg h_safe]; rw [dif_pos h_nonempty]; exact h_nonempty.choose_spec
    . intro h_safe
      unfold safetyFilter
      rw [dif_pos]; exact h_safe


axiom existsOptimalPolicy (c : @cost n_x n_u):
  ∃ (π_task : @policy n_x n_u), ∀ (x0 : @StateSpace n_x), ∀ (π : @policy n_x n_u),
  c x0 π_task ≤ c x0 π ∧
  ∃ (u_k : @InputSpace n_u) (filter : @StateSpace n_x → @InputSpace n_u → @InputSpace n_u),
    ∀ (x_k : @StateSpace n_x), u_k = filter x_k (π_task x_k)


lemma failureSetSafetyFunc (s : safetyValueFunction) (f : FailureSet s) (x : @StateSpace n_x) :
    x ∈ f.carrier → s x < 0 := by
  simp [f.isFailureSet]

theorem safetyFilterPreservesSafety
  (s : safetyValueFunction) (dyn : dynamics) (filter : SafetyFilter s dyn (n_x := n_x) (n_d := n_d))
  (f : FailureSet s) (η₀ : @InfoState n_d):

  filter.safetyMonitor.monitor η₀ (filter.fallback η₀) ≥ 0 →
  ∀ (x : @StateSpace n_x) (u : @InputSpace n_u) (d : @DistSpace n_d),
  dyn x (filter.intervention η₀ u) d ∉ f.carrier := by
    intro h x u d h_unsafe_filter

    have h_safety : filter.safetyMonitor.monitor η₀ (filter.intervention η₀ u) ≥ 0
      := filter.safetyCondition η₀ u h

    have h_valFunc : s (filter.safetyMonitor.dyn η₀ (filter.safetyMonitor.fallback η₀) d) ≥ 0
      := (filter.safetyMonitor.safetyCondition η₀ u (filter.interventionProp η₀ u h_safety)).right d

    have : s (dyn x (filter.intervention η₀ u) d) < 0 := by
      exact failureSetSafetyFunc s f (dyn x (filter.intervention η₀ u) d) h_unsafe_filter

    have h_safetyGuarantee : filter.safetyMonitor.monitor η₀ (filter.intervention η₀ u) ≥ 0 →
      s (dyn x (filter.intervention η₀ u) d) ≥ 0
      := filter.safetyMonitor.observableSafetyCondition η₀ (filter.intervention η₀ u) x d

    linarith [this, h_safetyGuarantee h_safety]
