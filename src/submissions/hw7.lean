import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  intros xy asym,
  apply not.intro,
  assume refl,
  cases xy,
  have rxx : r xy_w xy_w := refl xy_w,
  apply asym rxx,
  apply rxx,
end

/-

-/
/-
The proposition is not true without the condition that β is inhabitied, because
in the case of an empty set the relation cannot be irreflexive.
-/


/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example :(∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  intros ex trans refl,
  assume asym,
  cases ex with b t,
  have rbb : r b b := refl b,
  apply asym rbb,
  apply rbb,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  intros,
  apply set.ext,
  intros,
  split,
  -- 1
    assume xs1,
    apply ᾰ xs1,
  -- 2
    assume xs2,
    apply ᾰ_1 xs2,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  unfold divides,
  intros,
  apply exists.intro (n:ℕ),
  ring,
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  intros,
  unfold divides,
  apply exists.intro (1:ℕ),
  ring,
end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  intros,
  apply exists.intro (1:ℕ),
  ring,
end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  intros x y z,
  intros ex1 ex2,
  cases ex1 with w pf1,
  cases ex2 with w pf2,
  apply exists.intro w _,
  apply eq.trans pf2,
  ring,
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  intros x y a1 a2,
  cases a1 with w1 pf1,
  cases a2 with w1 pf2,
  apply eq.subst 
end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  intros a x,
  apply not.intro,
  assume rxx,
  apply a rxx,
  apply rxx,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  intros a a1 x y rxy,
  apply not.intro,
  assume ryx,
  
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  intros a1 a2 a3,

end


end relation
