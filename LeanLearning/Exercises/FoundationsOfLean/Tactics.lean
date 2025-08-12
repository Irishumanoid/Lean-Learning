variable (p : Type → Prop)
variable (r : Prop)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h (Exists.intro x hp)
  . intro h hepx
    apply Exists.elim hepx
    intro x hpa
    exact h x hpa

example (p : Nat → Prop) (h : ∀ (x : Nat) , p x) : p 14 := by
  apply h

theorem identity_thm (q : Prop) : q → q := id
example (q : Nat → Prop) : (∀ x, q x) → ∀ x, q x := by
  apply identity_thm

example (c : Type) (h : p c) : ∃ x, p x := by
  apply Exists.intro c
  assumption


structure Point where
  x : Int
  y : Int

def h : Point := {x := 1, y := 1}


#print And -- structure

example (p : Prop): p → (p ∧ p) :=
  λ hp => ⟨hp, hp⟩


example (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x := by
  intro h
  exact ⟨c, h c⟩

example : ∃ (p : Point) , p.x = 0 :=  by
  exact ⟨ ⟨ 0, 0 ⟩, rfl ⟩


example (p q : Prop) : p ∧ q → q := by
  intro ⟨_, hq⟩
  exact hq

example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨x, hnp⟩ hap
  exact hnp (hap x)

example (P Q : Type → Prop): (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨x, ⟨hp, hq⟩⟩
  exact ⟨x, ⟨hq, hp⟩⟩


theorem asd : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro hnpx x hpx
    exact hnpx ⟨x, hpx⟩
  . intro hnpx ⟨x, hpx⟩
    exact (hnpx x) hpx


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨x, ⟨hpx, hr⟩⟩
    exact ⟨⟨x, hpx⟩, hr⟩
  . intro ⟨⟨x, hpx⟩, hr⟩
    exact ⟨x, ⟨hpx, hr⟩⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro hnpx x hpx
    exact hnpx ⟨x, hpx⟩
  . intro hnpx ⟨x, hpx⟩
    exact hnpx x hpx

#print Exists
example : ∃ n , n > 0 := by
  let m := 1
  exact ⟨ m, Nat.one_pos ⟩
