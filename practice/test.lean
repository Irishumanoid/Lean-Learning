import Mathlib.Tactic.Linarith

#eval 1+2

example (x y z : ℚ)
        (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith

#check 1
#check "1"
#check ∃ (x : Nat) , x > 0
#check λ x => x+1
#check (4,5)
#check ℕ × ℕ
#check Type
#check Type → (Type → Type)
#check (Type → Type) → Type
def A := Type
def B := Type → Type
#check A → B
variable (x : A)
variable (f : A → A)
#check f (f (f x))
#check λ (g : A → A) => (λ (y : A) => g y)
#check λ (g : A → A) (y : A) => g y

example (p : Prop) : p → p :=
  λ h => h

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) :=
  λ ⟨ hpq, hqr ⟩ hp => hqr (hpq hp)

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  intro h hp
  have hpq := h.left
  have hqr := h.right
  exact hqr (hpq hp)


variable (X : Type)
variable (a : X)

#check λ (g : X → X) => (λ (x: X) => g x)
#reduce (λ (g : X → X) => λ (x: X) => g x) (λ x => x) a

def h₁ := λ (y : A) => y
def h₂ := λ (g : A → A) => λ (y : A) => g y

#check x
#check h₁
#check h₂
#check h₁ x
#check h₂ h₁               --> Example of currying
#check h₂ h₁ x

#reduce (types:=true) (λ (y : A) => y) x
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y)
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y) x

def α := Type

def c₀ := λ ( f : α → α ) => λ ( x : α ) => x
def c₁ := λ ( f : α → α ) => λ ( x : α ) => f x
def c₂ := λ ( f : α → α ) => λ ( x : α ) => f (f x)
def c₃ := λ ( f : α → α ) => λ ( x : α ) => f (f (f x))

#check c₀
#check c₁
#check c₂
def N := (α → α) → α → α
#check N

def succ := λ (m : N) (f : α → α) (x : α) => f (m f x)
#check succ
#reduce (types := true ) succ c₀
#reduce (types := true ) succ c₃

def add := λ (m n : N) (f : α → α) (x : α) => m f (n f x)
-- applies f 2+3=5 times
#reduce (types := true ) add c₂ c₃

-- each (n f) composed some number of times in m
def mul := λ (m n : N) (f : α → α) (x : α) => m (n f) x
#reduce (types := true ) mul c₂ c₃

def ifzero :=
  λ (m n p : N) (f : α → α) (x: α) =>
  n (λ _ => p f x) (m f x)
#reduce (types := true ) ifzero c₀ c₁ c₂

theorem one_plus_one_is_two : add c₁ c₁ = c₂ := rfl
theorem one_times_two_is_two : mul c₁ c₂ = c₂ := rfl

#check λ _ y => y
#check λ (g : α → α) y => g (g y)
#check λ (m n : N) f x => m (n f) x


example (p : Prop) : p → p :=
  λ hp => hp
example (p q : Prop) : p → (p → q) → q :=
  λ hp => λ hpq => hpq hp

#check (λ α x: Type => α → x) -- generic/polymorphic identity function
def my_id {α : Type u} (x : α) := x --curly braces to force type inference
#check my_id "hi"
#check my_id 1
#check my_id my_id my_id
#check List (List Nat)
#check [1,2,3]
#check Vector Nat 10

example : p∧q → p :=
  λ hpq => hpq.left

theorem t (p q: Prop) : ¬p → (p → q) :=
  λ hnp => λ hp => False.elim (hnp hp)

example : p → (p ∨ q) :=
  λ hp => Or.inl hp

example : (p ∨ q) → (q ∨ p) :=
  λ hpq => Or.elim hpq (λ hp => Or.inr hp) (λ hq => Or.inl hq)


-- Curry-Howard isomorphism
-- (propositional logic with only implication (→) is isomorphic to the simply typed λ-calculusis isomorphic to the simply typed λ-calculus)
variable {A C : Prop}

theorem my_theorem : A → A :=
  λ hA => hA

theorem appl_theorem_1 : (C → A) → C → A :=
  λ hca => λ hc => hca hc
theorem appl_theorem_2 : (C → A) → C → A :=
  λ hca => my_theorem hca

example : A → C → A := λ ha _ => ha


variable (p q: Prop)

example : p → ¬p → q :=
  λ hp hnp => absurd hp hnp

example : (p → q) → (¬q → ¬p) :=
  λ hpq hnq hp => absurd (hpq hp) hnq


-- Inductive Types
