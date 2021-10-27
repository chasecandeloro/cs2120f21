import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
has property p to a value of type β it is 
implied that there is a value of type β
with property q , then it is implied that the
existance of a value a of type α such that the predicate
p applied to a implies that there exists a value b
of type β with property q."
-/


-- Give your formal proof here
begin
  assume h,
  assume a,
  cases a with w1 pf1,
  cases h with f pf2,
  apply exists.intro (f w1),
  apply pf2 w1,
  apply pf1,
end
  
/-
Informal Proof:
Assume that there exists a function f that maps
all values of type α to type β such that a value a
of type α with property p implies a value b of type
β with property q. Assume that there exists some value
a of type α such that a has property p. Apply the mapping
function to the witness of the assumed proof of the existence
of value a with property p to create a value of type β. Apply
the assumed proof that a with property p implies b with
propery q to the witness of the assumed proof the existence
of a value a with property p to create a proof of property q.
Then use the previously created value of type β as a witness
and the assumed proof of property p for a value of type α to
prove the existence of a value of type β with property q.
QED.
-/
