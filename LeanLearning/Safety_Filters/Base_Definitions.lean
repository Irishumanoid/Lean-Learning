import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Basic

open RealInnerProductSpace

variable {n n_u n_d n_h : ℕ}
notation "ℝ^{" n "}" => EuclideanSpace ℝ (Fin n)

variable {𝓗 : Type*} [PseudoEMetricSpace 𝓗] -- can be a set or probability distribution
instance {n_d : ℕ} : Zero (ℝ^{n_d}) := ⟨λ _ => 0⟩

abbrev dynamics := 𝓗 → ℝ^{n_u} → ℝ^{n_d} → 𝓗 -- f
def measurement := 𝓗 → ℝ^{n_u} → ℝ^{n_d} → 𝓗 -- h
def cost := 𝓗 → (𝓗 → ℝ^{n_u}) → ℝ -- J (input -> policy -> value)


def safetyValueFunction := 𝓗 → ℝ
def isSafeSet (s : safetyValueFunction) (Ω : Set (𝓗)) := ∀ x ∈ Ω, s x ≥ 0

structure FailureSet (s : safetyValueFunction) where
  carrier: Set 𝓗
  isFailureSet: carrier = {x | s x < 0}

structure ConstraintSet (s : safetyValueFunction) (failureSet : FailureSet s) where
  carrier: Set (𝓗)
  no_overlap : Disjoint carrier failureSet.carrier

structure SafeSet (s : safetyValueFunction) where
  carrier: Set (𝓗)
  safetyCondition: isSafeSet s carrier

def maxSafeSet (s : @safetyValueFunction 𝓗) : SafeSet s := {
  carrier := {x | s x ≥ 0}
  safetyCondition := by
    intro x hx
    exact hx
}

def safeSubsetMax (s : @safetyValueFunction 𝓗) (safeSet : SafeSet s) :
  safeSet.carrier ⊆ (maxSafeSet s).carrier := by
    intro x hx
    have : s x ≥ 0 := safeSet.safetyCondition x hx
    exact this


structure SafePolicy where
  safetyValFunc : 𝓗 → ℝ
  safeSet : SafeSet safetyValFunc
  dyn : @dynamics n_u n_d 𝓗
  dist : ℝ^{n_d}
  invariance: ∃ (p : 𝓗 → ℝ^{n_u}), ∀ x ∈ safeSet.carrier, dyn x (p x) dist ∈ safeSet.carrier

structure SafetyMonitor (safetyValFunc : 𝓗 → ℝ)
(dyn : @dynamics n_u n_d 𝓗) (f_eta : FailureSet safetyValFunc) where
  monitor: 𝓗 → ℝ^{n_u} → ℝ
  fallback: 𝓗 → ℝ^{n_u}
  safetyCondition:
    ∀ (η : 𝓗) (u : ℝ^{n_u}), monitor η u ≥ 0 →
    η ∉ f_eta.carrier ∧ (∀ d : ℝ^{n_d}, safetyValFunc (dyn η (fallback η) d) ≥ 0)


structure SafetyFilter (safetyValFunc : 𝓗 → ℝ)
  (dyn : @dynamics n_u n_d 𝓗) (f_eta : FailureSet safetyValFunc) where
  fallback: 𝓗 → ℝ^{n_u}
  safetyMonitor: SafetyMonitor safetyValFunc dyn f_eta (n_u := n_u) (n_d := n_d)
  intervention: 𝓗 → ℝ^{n_u} → ℝ^{n_u}
  safetyCondition:
    ∀ (η : 𝓗) (u : ℝ^{n_u}),
    safetyMonitor.monitor η (fallback η) ≥ 0 → safetyMonitor.monitor η (intervention η u) ≥ 0
  interventionProp:
    ∀ (η : 𝓗) (u : ℝ^{n_u}),
    safetyMonitor.monitor η (intervention η u) ≥ 0 → safetyMonitor.monitor η u ≥ 0


-- keeps next system state within maximal safe set
def U_safe (x : 𝓗) (dyn : @dynamics n_u n_d 𝓗) (s : @safetyValueFunction 𝓗)
  : Set (ℝ^{n_u}) :=
    {u | ∀ d : ℝ^{n_d}, dyn x u d ∈ (maxSafeSet s).carrier}

/-
  Proposition 1 (perfect safety filter):
  ∃ filter, filter(x, s) ∈ U_safe (U_safe ⊆ U) if U_safe ≠ ∅ AND filter(x, s) = u if u ∈ U_safe
-/
noncomputable
def safetyFilter (dyn : @dynamics n_u n_d 𝓗) (s : @safetyValueFunction 𝓗) :
  𝓗 → ℝ^{n_u} → ℝ^{n_u} := by
  intro x u
  by_cases h : u ∈ U_safe x dyn s
  . exact u
  . by_cases h_nonempty : (U_safe x dyn s).Nonempty
    . exact h_nonempty.choose
    . exact u

theorem perfectSafetyFilter
  (dyn : @dynamics n_u n_d 𝓗)
  (s : safetyValueFunction):
  ∃ filter : 𝓗 → ℝ^{n_u} → ℝ^{n_u},
  ∀ (x : 𝓗) (u : ℝ^{n_u}),
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


axiom existsOptimalPolicy (c : @cost n_u 𝓗):
  ∃ (π_task : 𝓗 → ℝ^{n_u}), ∀ (x0 : 𝓗), ∀ (π : 𝓗 → ℝ^{n_u}),
    c x0 π_task ≤ c x0 π ∧
    ∃ (u_k : ℝ^{n_u}) (filter : 𝓗 → ℝ^{n_u} → ℝ^{n_u}),
      ∀ (x_k : 𝓗), u_k = filter x_k (π_task x_k)


-- since safety filter preserves the positivity of the safety monitor’s checks
axiom safetyMonitorGuaranteesSafety (η : 𝓗) (s : safetyValueFunction) (dyn : dynamics)
  (f_eta : FailureSet s) (filter : SafetyFilter s dyn f_eta (n_d := n_d)):
  ∀ (x : 𝓗) (u : ℝ^{n_u}) (d : ℝ^{n_d}),
  filter.safetyMonitor.monitor η (filter.intervention η u) ≥ 0 →
  s (dyn x (filter.intervention η u) d) ≥ 0


lemma failureSetSafetyFunc (s : safetyValueFunction) (f_eta : FailureSet s) (x : 𝓗) :
    x ∈ f_eta.carrier → s x < 0 := by
  simp [f_eta.isFailureSet]

theorem safetyFilterPreservesSafety (s : safetyValueFunction) (dyn : dynamics) (f_eta : FailureSet s)
  (filter : SafetyFilter s dyn f_eta (n_d := n_d)) (η₀ : 𝓗):

  filter.safetyMonitor.monitor η₀ (filter.fallback η₀) ≥ 0 →
  ∀ (x : 𝓗) (u : ℝ^{n_u}) (d : ℝ^{n_d}),
  dyn x (filter.intervention η₀ u) d ∉ f_eta.carrier := by
    intro h x u d h_unsafe_filter

    have h_safety : filter.safetyMonitor.monitor η₀ (filter.intervention η₀ u) ≥ 0
      := filter.safetyCondition η₀ u h

    have h_valFunc : s (dyn η₀ (filter.safetyMonitor.fallback η₀) d) ≥ 0
      := (filter.safetyMonitor.safetyCondition η₀ u (filter.interventionProp η₀ u h_safety)).right d

    have h_safetyGuarantee : filter.safetyMonitor.monitor η₀ (filter.intervention η₀ u) ≥ 0 →
      s (dyn x (filter.intervention η₀ u) d) ≥ 0
      := by apply safetyMonitorGuaranteesSafety

    have : s (dyn x (filter.intervention η₀ u) d) < 0 := by
      exact failureSetSafetyFunc s f_eta (dyn x (filter.intervention η₀ u) d) h_unsafe_filter

    linarith [this, h_safetyGuarantee h_safety]
