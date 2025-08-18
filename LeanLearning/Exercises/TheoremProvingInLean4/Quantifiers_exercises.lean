import Mathlib.Data.Set.Basic
open Classical
open Set

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro h
  match h with
  | ⟨_, r⟩ => exact r

example (a : α) : r → (∃ _ : α, r) := by
  intro h
  exact ⟨a, h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro h
    cases h with | intro x hpxr => exact ⟨⟨x, hpxr.left⟩, hpxr.right⟩
  . intro h
    obtain ⟨hpx, hr⟩ := h
    cases hpx with | intro a hpa => exact ⟨a, ⟨hpa, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro h
    cases h with | intro a h =>
      cases h with
      | inl hp => exact Or.inl ⟨a, hp⟩
      | inr hq => exact Or.inr ⟨a, hq⟩
  . intro h
    cases h with
    | inl hpx =>
      cases hpx with | intro a hp =>
      exact ⟨a, Or.inl hp⟩
    | inr hqx =>
      cases hqx with | intro a hq =>
      exact ⟨a, Or.inr hq⟩


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h hap
    obtain ⟨a, hnap⟩ := hap
    exact hnap (h a)
  . intro h a
    by_contra hnp
    have : ∃ x, ¬ p x := ⟨a, hnp⟩
    exact h this

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro hpx h
    obtain ⟨a, hpa⟩ := hpx
    exact h a hpa
  . intro h
    by_contra hnpx
    apply h
    intro x hpx
    exact hnpx ⟨x, hpx⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro h a hpa
    exact h ⟨a, hpa⟩
  . intro h hepx
    exact Exists.elim hepx (λ a ha => h a ha)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . intro h
    by_contra hnep
    apply h
    intro a
    by_contra hnx
    exact hnep ⟨a, hnx⟩
  . intro h hapx
    obtain ⟨a, hpa⟩ := h
    exact hpa (hapx a)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h hpx
    obtain ⟨x, px⟩ := hpx
    exact h x px
  . intro h a ha
    exact h ⟨a, ha⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro h hapx
    obtain ⟨x, hpr⟩ := h
    exact hpr (hapx x)
  . intro h
    by_cases hap : ∀ x, p x
    . use a
      intro _
      exact h hap
      -- OR: exact ⟨a, λ _ => h hap⟩
    . by_contra hnex
      have hap : ∀ x, p x := by
        intro x
        by_contra hnp
        have hex : ∃ x, p x → r := ⟨x, λ hp => absurd hp hnp⟩
        exact hnex hex
      have : ∃ x, p x → r := by
        use a
        intro _
        exact h hap
      exact hnex this

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro h hr
    obtain ⟨a, hrp⟩ := h
    exact ⟨a, hrp hr⟩
  . intro h
    by_contra hnrp
    push_neg at hnrp
    have : r ∧ ¬p a := hnrp a
    have hep : ∃ x, p x := h this.left
    obtain ⟨x, hpx⟩ := hep
    exact (hnrp x).right hpx


variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro x
      exact (h x).left
    . intro x
      exact (h x).right
  . intro hapq x
    obtain ⟨hp, hq⟩ := hapq
    exact ⟨hp x, hq x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hap x
  exact (h x) (hap x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl hp => exact Or.inl (hp x)
  | inr hq => exact Or.inr (hq x)


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  constructor
  intro har
  exact har x
  intro hr _
  exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  intro h
  by_cases ha : ∀ x, p x
  . exact Or.inl ha
  . apply Or.inr (by
      by_contra hnr
      apply ha
      intro x
      cases h x with
      | inl hpx => exact hpx
      | inr hr => exact absurd hr hnr
    )
  intro h
  cases h with
  | inl hap =>
    intro x
    exact Or.inl (hap x)
  | inr hr =>
    intro x
    exact Or.inr hr


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h_barber := h barber
  by_cases hb : shaves barber barber
  . have := h_barber.mp hb
    exact absurd hb this
  . have := h_barber.mpr hb
    exact absurd this hb
