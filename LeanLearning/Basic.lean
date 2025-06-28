def hello := "world"

#eval hello


theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
    have hp : p := And.left hpq
    have hq : q := And.right hpq
    show q ∧ p from And.intro hq hp



def α : Type := Nat

#check List α#check List Nat
#check Type


#check Type#check Type 1#check Type 2#check Type 3#check Type 4
#check List
#check Prod


def F.{u} (α : Type u) : Type u := Prod α α
#check F

#eval (λ x => x + 5) 10

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0
-- output applies v to x, then applies u to the result (γ  as output)
#eval (λ (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0

def double (x : Nat) : Nat :=
  x + x
#eval double 2

def square (x : Nat) : Nat :=
  x * x

def pi := 3.14159

def greater (x y : Nat) : Nat :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) :=
  f (f x)
#eval doTwice double 5


#eval let y := 2; y*y
def twice_double (x : Nat) : Nat :=
  let y := x + x; y*y
#eval twice_double 4
#eval let y := 2; let z := y^y; z*z
def t (x : Nat) : Nat :=
  let y := x * x
  y * y
#eval t 5

-- scoping variables
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwiceAbstract := h (h x)
  def doThriceAbstract := h (h (h x))

  #print compose
  #eval compose Nat Nat Nat double double 10
  #eval compose Nat Nat Nat double square 3
end useful

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  namespace Bar
    def ffa : Nat := f (f a)

  #check a  #check f  #check fa  #check ffa

#check Foo.a#check Foo.f#check Foo.fa#check Foo.ffa
#check Foo.Bar.ffa

open Foo
#check a#check f#check fa#check Foo.fa


def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
#check cons
#check cons Nat
#check cons Bool

-- use universe to define polymorphic constants
universe u v
def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨ a, b ⟩
def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b
def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2
#eval h1 5


-- implicit arguments when put in curly braces
def ident.{h} {α : Type h} (x : α) := x
#check (ident)
#check ident "hello"
#check @ident -- make arguments explicit
