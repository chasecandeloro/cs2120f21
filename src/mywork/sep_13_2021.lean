namespace implies
axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q

-- assume P is true
-- assume we have a proof of P (p)
axiom p : P

axiom pq : P → Q
-- assume that we have a proof, pq, of P → Q

-- intro for implies: assume premise, show conclusion
-- elimination rule for implies: apply proof of P → Q to a proof of P

end implies

namespace all
/-
FORALL
-/

axioms
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)

-- Does t have property P?
-- Yes, all objects of type T have property P

example : P t := a t

#check a t

end all

/-
AND & →
-/

axioms (P Q : Prop)

/-
Want a proof P ∧ Q.
-/