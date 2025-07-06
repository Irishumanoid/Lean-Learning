def Implies (p q : Prop) : Prop := p → q

#check And #check Or #check Not #check Implies
variable (p q r : Prop)

#check And p q #check Or (And p q) r #check Implies (And p q) (And q p)


structure Proof (p : Prop) : Type where
  proof : p

#check Proof
axiom and_commut (p q : Prop) : Proof ( Implies (And p q) (And q p))

variable (p q : Prop)
#check and_commut p q

-- a proof of Implies p q and a proof of p => a proof of q
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p → Proof q

-- p q : Prop, then p → q : Prop
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (p → q) -- Implies p q <==> p → q

set_option linter.unusedVariables false
variable {p q : Prop}
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
#print t1

variable (r s : Prop)
#check t1 p q
#check t1 r s
#check t1 (r → s) (s → r)
variable (h : r → s)
#check t1 (r → s) (s → r) h

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p => show r from h₁ (h₂ h₃)
#print t2

#check p → q → p ∨ q
#check ¬p → p → False
example (hp: p) (hq : q) : p ∧ q := And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q ) : q ∧ p := And.intro h.right h.left
variable (hp: p) (hq : q)

-- angle brackets instead of And.intro
#check (⟨hp, hq⟩ : p ∧ q)
theorem h1 (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (h : p ∧ q ∧ r) : r ∧ q ∧ p :=
  ⟨ h.right.right, ⟨h.right.left, h.left⟩ ⟩

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p => show False from hnq (hpq hp)
-- anything follows from a contradiction
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp


variable (p q : Prop)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨ h.right, h.left ⟩, fun h => ⟨ h.right, h.left ⟩ ⟩

-- Iff.mp gets p → q from p ↔ q
example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
-- suffices proves original goal (q ∧ p) with hypothesis (hq : q)
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h


-- useful for proofs by contradiction
open Classical
#check em p -- added by Classical logic
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    -- applying h : ¬p → false to hnp : ¬p gives contradiction
    (fun hnp : ¬p => absurd hnp h)

theorem em_from_dne (dne : ∀ {p : Prop}, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
  fun p =>
    dne (fun h : ¬(p ∨ ¬p) =>
      let hp : ¬p := fun hp => h (Or.inl hp) -- RHS takes in p and returns false
      h (Or.inr hp) -- contradiction since both conditions in the OR statement are false
    )

-- alternative proofs of dne
example (h: ¬¬p) : p :=
  byCases
  (fun hp : p => hp)
  (fun hnp : ¬p => absurd hnp h)

example (h: ¬¬p) : p :=
  byContradiction
  (fun hp : ¬p =>
   show False from h hp) -- h is function that takes ¬p to false

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    -- if p is true, show ¬q
    (fun hp : p =>
      Or.inr
        -- contradiction that shows q → False
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
