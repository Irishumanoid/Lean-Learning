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

-- disjoint collections of state vectors
structure FailureSet (n_x : ℕ) where
  carrier: Set (@StateSpace n_x)
structure ConstraintSet (n_x : ℕ) (failureSet : @FailureSet n_x) where
  carrier: Set (@StateSpace n_x)
  no_overlap : Disjoint carrier failureSet.carrier
-- TODO add condition that safe set entries make value vector positive
structure SafeSet (n_x : ℕ) where
  carrier: Set (@StateSpace n_x)


def policy {n_x n_u : ℕ} := @StateSpace n_x → @InputSpace n_u

def dynamics {n_x n_u n_d : ℕ} := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @StateSpace n_d
def measurement {n_x n_u n_d : ℕ} := @StateSpace n_x → @InputSpace n_u → @DistSpace n_d → @InfoState n_h
def cost {n_x n_u : ℕ} := @StateSpace n_x → @policy n_x n_u → ℝ -- J



theorem policyAppl : ∃ policy, ∀ x ∈ SafeSet, dynamics x (policy x) 0 ∈ SafeSet
example : ∀ x ∈ InputSpace, x ∉ FailureSet

-- define safety monitor and fallback policy (defs)


-- define control invariance (boolean function) using omega (subset of X → Prop)

-- prop 1
