/- Prove the following identities, replacing the "sorry" placeholders with actual proofs. -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun (h: p ∧ q) => ⟨h.right, h.left⟩)
    (fun (h: q ∧ p) => ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (h: p ∨ q) => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun (h: q ∨ p) => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (h: (p ∧ q) ∧ r) => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun (h: p ∧ (q ∧ r)) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun (h: (p ∨ q) ∨ r) => 
      h.elim (fun hpq => hpq.elim (fun hp => Or.inl hp) (fun hq => sorry)) (fun hr => sorry))
    (fun (h: p ∨ (q ∨ r)) => sorry)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun (h: p ∧ (q ∨ r)) => sorry)
    (fun (h: (p ∧ q) ∨ (p ∧ r)) => sorry)
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun (h: p ∨ (q ∧ r)) => sorry)
    (fun (h: (p ∨ q) ∧ (p ∨ r)) => sorry)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (h: p → (q → r)) => sorry)
    (fun (h: (p ∧ q → r)) => sorry)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun (h: (p ∨ q) → r) => sorry)
    (fun (h: (p → r) ∧ (q → r)) => sorry)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun (h: ¬(p ∨ q)) => sorry)
    (fun (h: ¬p ∧ ¬q) => sorry)
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p :=
  Iff.intro
    (fun (h: p ∨ False) => sorry)
    (fun (h: p) => sorry)
example : p ∧ False ↔ False :=
  Iff.intro
    (fun (h: p ∧ False) => sorry)
    (fun (h: False) => sorry)
example : (p → q) → (¬q → ¬p) := sorry
