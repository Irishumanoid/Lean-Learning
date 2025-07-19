example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y, q y :=
  λ h y => (h y).right

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

-- explicitly use a, b, and c (also don't define implicitly) for better type inference
#check trans_r
#check trans_r hab hbc


variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := by simp
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2 -- Eq.subst h1 h2

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.left_distrib (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.right_distrib x y x) ▸ (Nat.right_distrib x y y) ▸ h1
  Eq.trans h2 (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
