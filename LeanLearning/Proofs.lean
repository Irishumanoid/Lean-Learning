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
