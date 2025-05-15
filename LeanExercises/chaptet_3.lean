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
      h.elim (fun hpq => hpq.elim (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq))) (fun hr => Or.inr (Or.inr hr)))
    (fun (h: p ∨ (q ∨ r)) => 
      h.elim (fun hp => Or.inl (Or.inl hp)) (fun hpq => hpq.elim (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun (h: p ∧ (q ∨ r)) => 
      let ⟨hp, hqr⟩ := h
      hqr.elim 
      (fun hq => Or.inl ⟨hp, hq⟩) 
      (fun hr => Or.inr ⟨hp, hr⟩)
    )
    (fun (h: (p ∧ q) ∨ (p ∧ r)) => 
      h.elim 
      (fun hpq => let ⟨hp, hq⟩ := hpq; ⟨hp, Or.inl hq⟩) 
      (fun hpr => let ⟨hp, hr⟩ := hpr; ⟨hp, Or.inr hr⟩)
    )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun (h: p ∨ (q ∧ r)) =>
      h.elim
      (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
      (fun hqr => let ⟨hq, hr⟩ := hqr; ⟨Or.inr hq, Or.inr hr⟩))
    (fun (h: (p ∨ q) ∧ (p ∨ r)) => let ⟨hpq, hpr⟩ := h;
      hpq.elim
        (fun hp => Or.inl hp)
        (fun hq =>
          hpr.elim 
            (fun hp => Or.inl hp)
            (fun hr => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (h: p → (q → r)) => 
      (fun hpq =>
        let ⟨hp, hq⟩ := hpq
        h hp hq))
    (fun (h: (p ∧ q → r)) => 
      (fun hp => (fun hq => h ⟨hp, hq⟩))
    )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun (h: (p ∨ q) → r) => ⟨(fun hp => h (Or.inl hp)), (fun hq => h (Or.inr hq))⟩)
    (fun (h: (p → r) ∧ (q → r)) => 
      fun pq => 
        match pq with 
        | Or.inl hp => h.left hp
        | Or.inr hq => h.right hq)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun (h: ¬(p ∨ q)) => ⟨(fun hp => h (Or.inl hp)), (fun hq => h (Or.inr hq))⟩)
    (fun (h: ¬p ∧ ¬q) => 
      fun pq => 
        match pq with 
          | Or.inl hp => h.left hp
          | Or.inr hq => h.right hq)
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun h => 
    fun hpq =>
        match h with
        | Or.inl hnp => hnp hpq.left
        | Or.inr hnq => hnq hpq.right
example : ¬(p ∧ ¬p) := 
  fun h => h.right h.left

example : p ∧ ¬q → ¬(p → q) := 
  fun ⟨hp, hnq⟩ => 
    fun hpq => 
      hnq (hpq hp)

example : ¬p → (p → q) := 
  fun hnp hp => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) := 
  fun h hp =>
    match h with
    | Or.inl hnp => False.elim (hnp hp)
    | Or.inr hq => hq

example : p ∨ False ↔ p :=
  Iff.intro
    (fun (h: p ∨ False) => 
      match h with
      | Or.inl hp => hp
      | Or.inr f => False.elim f)
    (fun (hp: p) => 
      Or.inl hp
    )

example : p ∧ False ↔ False :=
  Iff.intro
    (fun (h: p ∧ False) => h.right)
    (fun (h: False) => And.intro (False.elim h) h)

example : (p → q) → (¬q → ¬p) := 
  fun h: p → q => 
  fun hnq : ¬q => 
  fun hp : p => 
  hnq (h hp)
