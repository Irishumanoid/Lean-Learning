-- First Order Logic (FOL)
variable (f : Nat → Nat)
-- ∀ x ∃ y , f x > y
#check ∀ x : Nat , ∃ y : Nat , f x > y


inductive Person where | mary | steve | ed | jolin
namespace Person
#check ed

-- predicates (Prop-valued functions)
def InSeattle (x : Person) : Prop := match x with
  | mary | ed => True
  | steve | jolin => False
variable (InWashington : Person → Prop)

example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr (λ h => h) -- False → False is ¬False=True (RHS)


def is_zero (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => False

example : ¬is_zero 91 :=  -- is_zero 91 → False
  λ h => h

theorem t : is_zero 0 := True.intro
theorem t1 : True := True.intro

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

def next_to (p q : Person) := on_right p q ∨ on_right q p

example : next_to mary steve :=
  Or.inl (Eq.refl steve)

example : ∀ (x : Person) , (InSeattle x) ∨ (¬InSeattle x) :=
  λ x => match x with
  | steve => Or.inr (λ h => h)
  | mary => Or.inl True.intro
  | ed => Or.inl True.intro
  | jolin => Or.inr (λ h => h)
#check (x : Person) → (InSeattle x) ∨ ¬(InSeattle x)


variable (α : Type) (P Q : α → Prop)

example : (∀ x : α, P x ∧ Q x) → ∀ y : α, P y :=
  λ h q => (h q).left

-- if P applies for all x : α, must apply for some x : α
example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  λ h => Exists.intro q (h q)

-- if some x satisfies conjunction of P x and Q x, there must be some x satisfying commutative version of it
example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h₁ (λ c h => Exists.intro c (And.intro h.right h.left))

-- proof examples
variable (p: Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (λ h => Exists.elim h (λ a h₁ => ⟨Exists.intro a (h₁.left), h₁.right⟩))
  (λ h => Exists.elim h.left (λ a h₁ => Exists.intro a ⟨h₁, h.right⟩))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (λ h x hp => h (Exists.intro x hp))
  (λ h hp => Exists.elim hp (λ a hx => h a hx))
