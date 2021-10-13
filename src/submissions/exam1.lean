/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
            (q : Q)
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume h,
  assume p,
  apply h p,
end

-- Extra credit [2 points]. Who invented this principle?

-- Aristotle

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- answer here

/-
The introduction rule for true states that there
is always a proof of true, as true is always true, so
the rule is to always return a proof of true.
-/

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- The introduction rule states that a proof
  that both P and Q are true, P ∧ Q, can be
  formed with an input of a proof of P and a
  proof of Q.

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/

/-

(P Q : Prop) (pq : P ∧ Q)
-------------------------- intro
      (p : P) (q : Q)

The elimination rule for ∧ states that given a proof
of an ∧ statement, a proof of both the left object and
the right object can be extracted.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (Q P : Prop), (Q ∧ P) → P := 
begin
  assume Q P,
  assume qandp,
  apply and.elim_right qandp,
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- answer here
/-
  The introduction rule for ∀ states to assume arbitrary
  but specific objects of the type being proved for. Then,
  by proving the proposition about the assumed arbitrary types,
  you can assert that proposition is true for all
  objects of the type because of the arbitrary nature of
  the objects.
-/

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (pf : (t : T), Q)

-- English language answer here

/-
The elimination rule for ∀ states that given a proof of a
proposition for all objects of a type and an object of that
type, a proof can be created of the proposition for that object.
-/

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- answer here
Because pf proves Q for any arbitrary object of type T, and,
because t is of type T, the elimination rule for ∀ can be applied
to pf and t to return a proof of Q for t.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- add answer here
  (Lynn : Person)
  -- add answer here
  (LynnKnowsLogic : KnowsLogic Lynn)
/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn:= 
begin
  apply LogicMakesYouBetterAtCS Lynn,
  apply LynnKnowsLogic,
end




-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- answer here
/-
The strategy of proof by negation entails proving
¬P by assuming P and showing that P → false. Once
it has been shown that P → false, P can be accepted
as not true because it leads to a contradiction in
logic as if P was true as false would be true.
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that ¬P → false.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classically valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (A B : Prop), (A ↔ B) → (B ↔ A):=
begin
  assume A B,
  assume aiffb,
  apply iff.intro,
  -- forward
    assume b,
    apply iff.elim_right aiffb,
    apply b,
  -- backward
    assume a,
    apply iff.elim_left aiffb,
    apply a,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 

/-
The proposition ELJL states that there is a type "person"
and that "nice" and "talented" are both propositions about a person.
Also "likes" is a proposition a person can have towards another
person.  The proposition also states that all people like any
person who is both nice and talented. Additionally, it states
that John Lennon is a person and that he is both nice and talented
and finally that everyone likes John Lennon.
-/

example : ELJL :=
begin
  intros ELJL,
  intros,
  have JLN := and.elim_left JLNT,
  have JLT := and.elim_right JLNT,
  apply elantp,
  apply JLN,
  apply JLT,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- answer here
    /-
    Car is heavy and red
    Car is heavy and blue
    Car is light and red
    Car is light and blue
    -/

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), (x = y) → (y = z) → (x = z)


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀  (P : Prop), ¬¬P ↔ (P ∨ ¬P)

example : negelim_equiv_exmid :=
begin
  intros P,
  apply iff.intro,
  -- forward
    assume nnp,
    admit,
  -- backward
    assume pornp,
    cases pornp,
    -- 1
      assume np,
      apply false.elim (np pornp),
    -- 2
end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : ((∀ (p: Person), ∃ (q : Person), (Loves p q)) ∧ (∀ (a b : Person), (Loves a b) → (Loves b a)))
 → (∃ (x : Person), ∀ (y : Person), Loves x y :=
 begin
   assume h,
   have sel := and.elim_left h,
   have sym := and.elim_right h,
   apply sym sel,
 end
