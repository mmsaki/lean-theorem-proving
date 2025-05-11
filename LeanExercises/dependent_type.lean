/- 
docs: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html 
-/
#check Nat × Nat → Nat
#check (0, 1)
#eval (2,3).2

universe u

def F (α: Type u) : Type u := Prod α α 

#check F
#check fun (x: Nat) => x + 5
#check λ (x: Nat) => x + 5
#check fun x => x + 5
#check λ x => x + 5 
#eval (λ x => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x: Nat) (y: Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n: Nat) : String := toString n
def g (s: String) : Bool := s.length > 0

#check fun x : Nat => x
#check fun x : Nat => true
#check fun (f: Nat → String) (g: String → Bool) (x: ℕ) => g (f x)

#check fun (α β γ: Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

namespace Foo
  def a : Nat := 5
  def f (x) := x + 7
  def fa := f a
  def ffa := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check ffa
#check Foo.ffa

#check List.nil
#check List.cons
#check List.map

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe v

def f2 (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨ a , b ⟩

def h1 (x: Nat) : Nat := 
  (f2 Type (fun α => α) Nat x).2

#eval h1 0

#check List

def Lst (α : Type u) : Type u := List α
def Lst.cons {α : Type u} (a: α) (as: Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil
#eval Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
#eval Lst.append as bs

#eval List.cons 5 List.nil 
#eval List.append (List.cons 10 List.nil) (List.cons 5 List.nil)

def ident {α : Type u} (x: α) := x

#check ident
#check ident 1
#check ident "hello"
#check @ident

section
  variable {α : Type u}
  variable (x: α)
  def identf := x
end

#check identf
#check identf 4
#check identf "hello"

#check List.nil
#check id
#check (List.nil : List Nat)
#check (id: Nat → Nat)

#check 2
#check (2: Nat)
#check (2: Int)

#check @id
#check @id Nat
#check @id Bool
#check @id Nat 1
#check @id Int 1
#check @id Bool true

