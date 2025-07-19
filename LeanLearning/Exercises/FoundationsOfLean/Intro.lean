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


-- new namespace to prevent type collisions with default libraries
namespace Temp
-- Inductive Types
inductive Two where
  | a : Two
  | b : Two

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

def Nat.plus (n m : Nat) := match n with
  | zero => m
  | succ x => succ (plus x m)

open Nat
#check succ (succ (succ zero))
#check zero.succ.succ.succ
#reduce plus (succ zero) (succ zero)


inductive Expr where
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr

def Expr.swap (e : Expr) := match e with
  | var s => var s
  | add x y => add y x
  | mul x y => mul y x
  | neg x => neg x

open Expr
#check add (var "x") (var "y")                          -- x+y
#check add (var "x") (mul (neg (var "y")) (var "z"))    -- x-yz
def e := add (var "x") (mul (neg (var "y")) (var "z"))
#reduce e
#reduce e.swap


def Two.toggle ( x : Two ) := match x with
  | Two.a => Two.b
  | Two.b => Two.a

open Two
#reduce toggle (toggle Two.a)


inductive NatList where
  | empty : NatList
  | cons : Nat → NatList → NatList -- takes a Nat and a NatList and adds the Nat to the NatList
namespace NatList
#check cons zero (cons zero empty) -- [0, 0]
#check (empty.cons zero).cons zero -- [0, 0]


inductive List {α : Type} where
  | empty : List
  | cons : α → List → List

namespace List
#check cons "hello" (cons "world" empty) -- ['hello', 'world']


-- Propositional connectives
def g (p q : Prop) : p → q → And p q :=
  λ hp => λ hq => And.intro hp hq

/-
                Γ ⊢ φ ∧ ψ                          Γ ⊢ φ ∧ ψ
  ∧-Elim-Left ——————————————         ∧-Elim-Right —————————————
                  Γ ⊢ φ                              Γ ⊢ ψ
-/
def And.left {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro hp _ => hp

def And.right {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro _ hq => hq

example (p q : Prop) : (And p q) → p :=
  λ hpq => And.left hpq

example (p q : Prop) : (And p q) → (And q p) :=
  λ hpq => And.intro hpq.right hpq.left

/-
                 Γ ⊢ φ                              Γ ⊢ ψ
 ∨-Intro-Left ———————————          ∨-Intro-Right ————————————
               Γ ⊢ φ ∨ ψ                          Γ ⊢ φ ∨ ψ
-/
inductive Or (Φ Ψ : Prop) : Prop where
  | inl (h : Φ) : Or Φ Ψ
  | inr (h : Ψ) : Or Φ Ψ

example (p q : Prop) : And p q → Or p q :=
  λ hpq => Or.inl hpq.left


/-
           Γ,p ⊢ r    Γ,q ⊢ r    Γ ⊢ p ∨ q
  ∨-Elim ————————————————————————————————————
                       Γ ⊢ r
-/
def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) : r :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

example (p q : Prop): Or p q → Or q p :=
  λ hpq => Or.elim hpq (λ hp => Or.inr hp) (λ hq => Or.inl hq)


inductive False : Prop
def Not (p : Prop) : Prop := p → False

/-
           Γ ⊢ ⊥
  ⊥-Elim ——————————
           Γ ⊢ p

Anything can be derived from False
-/
def False.elim {p : Prop} (h : False) : p := nomatch h

example (p q : Prop) : And p (Not p) → q :=
  λ h => False.elim (h.right h.left)

example : False → True :=
  λ h => False.elim h
