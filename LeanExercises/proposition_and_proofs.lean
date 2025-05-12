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

