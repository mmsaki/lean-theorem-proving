/- 
docs: https://github.com/leanprover/theorem_proving_in_lean4/blob/master/propositions_and_proofs.md
-/

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop): Type where
  proof : p

#check @And
#check @Or
#check @Not
#check @Implies
#check @Proof

variable (p q r: Prop)
#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

axiom and_comm2 (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm2 p q

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
#check @modus_ponens

axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
#check @implies_intro


-- Theorem
variable { p: Prop }
variable { q: Prop }

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
#print t1

theorem _t1 (hp: p) (hq : q) : p := hp
#check _t1

axiom hp : p
axiom hq : q
theorem t2 : q → p := t1 hp
theorem t3 : p → q → p := t1 hq
theorem t4 : p := hp

axiom unsound : False
-- everything follows from false
theorem ex : 1 = 0 := 
  -- false elimination
  False.elim unsound
  
theorem __t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp: p) (hq : q) => hp

variable {p q : Prop}
theorem ___t1 : p → q → p := fun (hp: p) (hq : q) => hp

theorem tt1 (p q : Prop) (hp: p) (hq: q) : p := hp
variable (p q r s : Prop)
#check tt1 p q
#check tt1 r s
#check tt1 (r → s) (s → r)

variable (h: r → s)
#check tt1 (r → s) (s → r) h 
variable (h1: s → r)
#check tt1 (r → s) (s → r) h h1

theorem tt2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
    show r from h₁ (h₂ h₃)

-- \not \and \or \impl \iff 
#check p → q → q ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- the order of operations is as follows, ¬, ∧, ∨, →, ↔.
-- order = not, and, or, impl, iff
-- a ∧ b → c ∨ d ∧ e == (a ∧ b) → (c ∨ (d ∧ e))

example (hp: p) (hq: q) : p ∧ q := And.intro hp hq
#check fun (hp: p) (hq: q) => And.intro hp hq

example (h: p ∧ q) : p := And.left h
example (h: p ∧ q) : q := And.right h
example (h: p ∧ q) : q ∧ p := 
  And.intro (And.right h) (And.left h)

variable (hp: p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

variable (xs: List Nat)

#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

example (h: p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩
example (h: p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

----------------- Disjunction -------------------------
-------------------------------------------------------
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

-- or elimination, proof that p ∨ q = q ∨ p
example (h: p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
-- more concise proof
example (h: p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

--------------- Negation & Falsity ----------------------
---------------------------------------------------------

/- negation, ¬p, is actually defined to be p → False -/
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hq : p =>
    show False from hnq (hpq hp)
/- the False has single elimination rule, False.elim -/
/- this rule is called 'ex falso' short for 'ex falso sequitur quodlibet' -/
/- 'the priciple of explosion' -/

example(hp: p) (hnp : ¬p) : q := False.elim (hnp hp)
/- the fact q follows from falsity, this pattern is deriving an arbitrary -/
/- fact from contradictory hypothesism, is quite common, and is representd by  -/
/- absurd -/
example (hp: p) (hnp: ¬p) : q := absurd hp hnp

/- here, for example, a proof of ¬p → q → (q → p) → r -/
example (hnp : ¬p) (hq : q) (hqp: q → p) : r :=
  absurd (hqp hq) hnp

---------------- Logical Equivalence ---------------------
----------------------------------------------------------

/- here if a proof for p ∧ q ↔ q ∧ p -/
variable (p q : Prop)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun h : p ∧ q =>
    show q ∧ p from And.intro (And.right h) (And.left h))
  (fun h : q ∧ p =>
    show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap

variable (h: p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap1 : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩
example (h: p ∧ q) : q ∧ p := (and_swap1 p q).mp h


------------ Introducing Auxiliary Subgoals -----------------
-------------------------------------------------------------


