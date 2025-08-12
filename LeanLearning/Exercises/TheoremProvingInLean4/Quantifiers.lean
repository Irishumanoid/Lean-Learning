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
  calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y
    := Nat.left_distrib (x + y) x y
  _ = x * x + y * x + (x * y + y * y)
    := by repeat rw [Nat.right_distrib]
  _ = x * x + y * x + x * y + y * y
    := by exact Eq.symm (Nat.add_assoc (x * x + y * x) (x * y) (y * y))

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.right_distrib, Nat.add_assoc]

variable (a b c d e : Nat)
example
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b := by rw [h1]
    _ ≤ c := by exact h2
    _ < c + 1 := by simp
    _ < d := by exact h3

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, ⟨hxy, hyz⟩⟩


variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h (λ w hw => ⟨w, ⟨hw.right, hw.left⟩⟩)
