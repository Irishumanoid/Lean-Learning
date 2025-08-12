import Mathlib.Data.Set.Basic
open Set

-- Exercises
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun ⟨hp, hq⟩ => ⟨hq, hp⟩)
    (fun ⟨hq, hp⟩ => ⟨hp, hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩)
    (fun ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩)
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
  (fun h: (p ∨ q) ∨ r =>
    match h with
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq)
    | Or.inr hr => Or.inr (Or.inr hr))
  (fun h: p ∨ (q ∨ r) =>
    match h with
    | Or.inl hp => Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => Or.inr hr)


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun ⟨hp, hqr⟩ =>
    match hqr with
    | Or.inl hq => Or.inl ⟨hp, hq⟩
    | Or.inr hr => Or.inr ⟨hp, hr⟩)
  (fun h : (p ∧ q) ∨ (p ∧ r) =>
    match h with
    | Or.inl ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩)
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun ⟨hp, hqr⟩ => hqr.imp (fun hq => ⟨hp, hq⟩) (fun hr => ⟨hp, hr⟩))
    (fun h => Or.elim h (fun ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩) (fun ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun h: p ∨ (q ∧ r) =>
    match h with
    | Or.inl hp => ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩)
  (fun ⟨hpq, hpr⟩ =>
    Or.elim hpq
      (fun hp => Or.inl hp)
      (fun hq => Or.elim hpr (fun hp => Or.inl hp) (fun hr => Or.inr ⟨hq, hr⟩)))

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
  (fun h : p → (q → r) =>
    fun (hpq: p ∧ q) => (h hpq.left) hpq.right)
  (fun (h: p ∧ q → r) =>
    fun (hp : p) (hq : q) => h ⟨hp, hq⟩)

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
  (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
  (fun ⟨hpr, hqr⟩ => fun hpq =>
    match hpq with
    | Or.inl hp => hpr hp
    | Or.inr hq => hqr hq)


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun h =>
    ⟨fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq)⟩)
  -- could also do: fun h hpq => Or.elim hpq h.left h.right
  (fun h => fun hpq => match hpq with
    | Or.inl hp => h.left hp
    | Or.inr hq => h.right hq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h hpq => match h with
  | Or.inl hnp => hnp hpq.left
  | Or.inr hnq => hnq hpq.right

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun h hpq => h.right (hpq h.left)

example : ¬p → (p → q) :=
  fun h hp => False.elim (h hp)

example : (¬p ∨ q) → (p → q) :=
  fun h => Or.elim h (fun hnp hp => False.elim (hnp hp)) (fun hq _ => hq)

example : p ∨ False ↔ p :=
  Iff.intro
  (fun h => match h with
    | Or.inl hp => hp
    | Or.inr hf => False.elim hf)
  (fun h => Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro (fun h => h.right) (fun h => False.elim h)

example : (p → q) → (¬q → ¬p) :=
  fun hpq hnq hp => hnq (hpq hp)


-- proof by contradiction scariness oof
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h => Or.elim (Classical.em q)
    (fun hq => Or.inl (fun _ : p => hq))
    (fun hnq => Or.inr (fun hp : p =>
      match h hp with
      | Or.inl hq => absurd hq hnq
      | Or.inr hr => hr))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => Or.elim (Classical.em p)
    (fun hp => Or.inr (fun hq => h ⟨hp, hq⟩))
    (fun hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h => Or.elim (Classical.em q)
    (fun hq => False.elim (h (fun _ : p => hq)))
    (fun hnq =>
      have hp : p := Classical.byContradiction (fun hnp =>
        h (fun hp => absurd hp hnp))
      ⟨hp, hnq⟩
      )

example : (p → q) → (¬p ∨ q) :=
  fun h => match Classical.em q with
  | Or.inl hq => Or.inr hq
  | Or.inr hnq =>
  have hnp : ¬p := fun hp => hnq (h hp)
  Or.inl hnp

example : (¬q → ¬p) → (p → q) :=
  fun hqp hp => match Classical.em q with
  | Or.inl hq => hq
  | Or.inr hnq => absurd hp (hqp hnq)

example : p ∨ ¬p := Classical.em p

example : (((p → q) → p) → p) :=
  fun h => match Classical.em p with
  | Or.inl hp => hp
  | Or.inr hnp => h (fun hp => False.elim (hnp hp))
