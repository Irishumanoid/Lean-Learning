
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

open Weekday
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay friday


namespace Test
inductive Prod (α : Type) (β : Type) where
  | mk : α → β → Prod α β

inductive Sum (α : Type) (β : Type) where
  | inl : α → Sum α β
  | inr : β → Sum α β

def aProd {α β : Type} (p : Prod α β) : α :=
  match p with
  | Prod.mk α _ => α

def bProd {α β : Type} (p : Prod α β) : β :=
  match p with
  | Prod.mk _ β => β

def prod_example (p : Prod Bool Bool) : Bool :=
  Prod.casesOn (motive := λ _ => Bool) p
    (λ b1 b2 => cond b1 (cond b2 true false) (cond b2 false true))

#eval prod_example (Prod.mk true true)
#eval prod_example (Prod.mk false true)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := λ _ => Nat) s
    (λ s => s + s * 5)
    (λ s => s ^ 2 + 11)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => Nat.succ (add m n)

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      0 + (n + 1) = (0 + n) + 1 := by rw [Nat.add_assoc]
      _ = n + 1                 := by rw [ih]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k with
  | zero => rfl
  | succ a ih => simp [Nat.add_succ (m+n) a, ih]; rfl

theorem succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
  | zero => simp
  | succ k ih =>
    calc
      Nat.succ n + Nat.succ k = Nat.succ (Nat.succ n + k) := rfl
      _ = Nat.succ (Nat.succ (n + k))                     := by rw [ih]


theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => rw [zero_add]; rfl
  | succ k ih =>
    calc
      m + Nat.succ k = Nat.succ (m + k) := rfl
      _ = Nat.succ (k + m)              := by rw [ih]
      _ = Nat.succ k + m                := by rw [succ_add]

def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => m + mul m n

def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n => n

def truncSub : Nat → Nat → Nat
  | n, 0 => n
  | 0, _ => 0
  | Nat.succ n, Nat.succ m => truncSub n m
#eval truncSub 4 2

def pow (n p : Nat) : Nat :=
  match p with
  | 0 => 1
  | Nat.succ p => mul n (pow n p)
#eval pow 3 4

variable (α : Type)
theorem append_nil (as : List α) : List.append as List.nil = as := by
  simp

theorem append_assoc (as bs cs : List α) :
    List.append (List.append as bs) cs = List.append as (List.append bs cs) := by
  simp


theorem length_sum (xs ys : List α): List.length (xs ++ ys) = List.length xs + List.length ys := by
  induction xs with
  | nil => rw [List.nil_append]; exact Nat.right_eq_add.mpr rfl
  | cons a lst ih =>
    simp only [List.cons_append, List.length_cons]
    calc
      List.length (a :: (lst ++ ys)) = 1 + List.length (lst ++ ys) := by
          rw [List.length_cons, List.length_append]; rw [add_comm]
      _ = lst.length  + 1  + ys.length := by rw [ih, ←add_assoc, add_comm 1 lst.length]


end Test


variable {α β : Type} {a b c : α}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
  rw [h₁]
  exact h₂

theorem congrEq (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
  rw [h]
