import Mathlib.Data.Set.Basic
open Set

-- Exercises
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ ⟨hp, hq⟩ => ⟨hq, hp⟩)
    (λ ⟨hq, hp⟩ => ⟨hp, hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ h : p ∨ q =>
      Or.elim h (λ hp => Or.inr hp) (λ hq => Or.inl hq))
    (λ h : q ∨ p =>
      Or.elim h (λ hq => Or.inr hq) (λ hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩)
    (λ ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩)
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨p, q⟩, r⟩; exact ⟨p, ⟨q, r⟩⟩
  · intro ⟨p, ⟨q, r⟩⟩; exact ⟨⟨p, q⟩, r⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    rcases h with ((hp | hq) | hr)
    · left; exact hp
    · right; left; exact hq
    · right; right; exact hr
  · intro h
    rcases h with (hp | (hq | hr))
    · left; left; exact hp
    · left; right; exact hq
    · right; exact hr

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (λ h: (p ∨ q) ∨ r =>
    match h with
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq)
    | Or.inr hr => Or.inr (Or.inr hr))
  (λ h: p ∨ (q ∨ r) =>
    match h with
    | Or.inl hp => Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => Or.inr hr)


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (λ ⟨hp, hqr⟩ =>
    match hqr with
    | Or.inl hq => Or.inl ⟨hp, hq⟩
    | Or.inr hr => Or.inr ⟨hp, hr⟩)
  (λ h : (p ∧ q) ∨ (p ∧ r) =>
    match h with
    | Or.inl ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩)
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ ⟨hp, hqr⟩ => hqr.imp (λ hq => ⟨hp, hq⟩) (λ hr => ⟨hp, hr⟩))
    (λ h => Or.elim h (λ ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩) (λ ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (λ h: p ∨ (q ∧ r) =>
    match h with
    | Or.inl hp => ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩)
  (λ ⟨hpq, hpr⟩ =>
    Or.elim hpq
      (λ hp => Or.inl hp)
      (λ hq => Or.elim hpr (λ hp => Or.inl hp) (λ hr => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  intro h hpq
  have hqr : q → r := h hpq.left
  exact hqr hpq.right
  intro h hp hq
  have hpq : p ∧ q := ⟨hp, hq⟩
  exact h hpq
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
  (λ h : p → (q → r) =>
    λ (hpq: p ∧ q) => (h hpq.left) hpq.right)
  (λ (h: p ∧ q → r) =>
    λ (hp : p) (hq : q) => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  intro h
  constructor
  intro hp
  exact h (Or.inl hp)
  intro hq
  exact h (Or.inr hq)
  intro ⟨hpr, hqr⟩ hpq
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (λ h => ⟨λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩)
  (λ ⟨hpr, hqr⟩ => λ hpq =>
    match hpq with
    | Or.inl hp => hpr hp
    | Or.inr hq => hqr hq)


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (λ h =>
    ⟨λ hp : p => h (Or.inl hp), λ hq : q => h (Or.inr hq)⟩)
  -- could also do: λ h hpq => Or.elim hpq h.left h.right
  (λ h => λ hpq => match hpq with
    | Or.inl hp => h.left hp
    | Or.inr hq => h.right hq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h hpq => match h with
  | Or.inl hnp => hnp hpq.left
  | Or.inr hnq => hnq hpq.right

example : ¬(p ∧ ¬p) :=
  λ h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  λ h hpq => h.right (hpq h.left)

example : ¬p → (p → q) :=
  λ h hp => False.elim (h hp)

example : (¬p ∨ q) → (p → q) :=
  λ h => Or.elim h (λ hnp hp => False.elim (hnp hp)) (λ hq _ => hq)

example : p ∨ False ↔ p :=
  Iff.intro
  (λ h => match h with
    | Or.inl hp => hp
    | Or.inr hf => False.elim hf)
  (λ h => Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro (λ h => h.right) (λ h => False.elim h)

example : (p → q) → (¬q → ¬p) :=
  λ hpq hnq hp => hnq (hpq hp)


-- proof by contradiction scariness oof
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h => Or.elim (Classical.em q)
    (λ hq => Or.inl (λ _ : p => hq))
    (λ hnq => Or.inr (λ hp : p =>
      match h hp with
      | Or.inl hq => absurd hq hnq
      | Or.inr hr => hr))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h => Or.elim (Classical.em p)
    (λ hp => Or.inr (λ hq => h ⟨hp, hq⟩))
    (λ hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  λ h => Or.elim (Classical.em q)
    (λ hq => False.elim (h (λ _ : p => hq)))
    (λ hnq =>
      have hp : p := Classical.byContradiction (λ hnp =>
        h (λ hp => absurd hp hnp))
      ⟨hp, hnq⟩
      )

example : (p → q) → (¬p ∨ q) :=
  λ h => match Classical.em q with
  | Or.inl hq => Or.inr hq
  | Or.inr hnq =>
  have hnp : ¬p := λ hp => hnq (h hp)
  Or.inl hnp

example : (¬q → ¬p) → (p → q) :=
  λ hqp hp => match Classical.em q with
  | Or.inl hq => hq
  | Or.inr hnq => absurd hp (hqp hnq)

example : p ∨ ¬p := Classical.em p

example : (((p → q) → p) → p) :=
  λ h => match Classical.em p with
  | Or.inl hp => hp
  | Or.inr hnp => h (λ hp => False.elim (hnp hp))
