/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
/-
The proposition true can always be proved using true.intro, because
by definition the proposition true states that a proposition has a proof.
-/


example : false := _    -- trick question? why?
/-
By definition, the proposition false states that a proposition has no
proof and thus it would be a contradiction for there to be a proof of false.
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
/-
Apply the introduction rule for ∀ by assuming an arbitrary proposition, P
and then apply then introduction rule for ↔ which creates two implication
statements that need to be proved. From there, prove the forward direction by assuming
a proof of  P ∨ P and applying the elimination rule for ∨. Then prove each case by 
assuming a proof of P, p, and then applying the proof. Finally, prove the backwards implication
by assuming a proof of P, p, and apply the intro rule for ∨ using the assumed proofs p and P.
QED.
-/
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
/-
Apply the introduction rule for ∀ by assuming an arbitrary proposition P, then apply
the introduction rule for ↔, generating two implication that need to be proven.
Prove the forward implication by assuming a proof of P ∧ P and applying the elimation
rule for ∧, which again creates two implications, which can be proven by assuming a proof
of P and then applying the assuming proof of P. Then prove the backwards direction by 
assuming a proof of P, p, and using it twice in the intro rule for ∧ to create a proof of
P ∧ P, thereby proving the statement.
QED.
-/
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandp,
    apply and.elim pandp,
    assume p,
    assume p,
    exact p,
  --backward
    assume p,
    apply and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
/-
Apply the introduction rule for ∀ by assuming arbitrary propositions P and Q. Then
apply the intro rule for ↔ to create two implications that need to be proved. Prove
the first by assuming a proof of P ∨ Q then by applying the ∨ elimination rule on the
proof, generating two implications to be proved. The first can be proved by assuming p, 
a proof of P and applying the right intro rule for ∨ with the proof of P. The second can
be proved by assuming a proof of Q and applying the left intro rule for ∨ using the proof
of Q. Now only the second implication from the ↔ intro rule must be proved, which is begun
by assuming a proof Q ∨ P and applying the ∨ elimination rule, which creates two implications,
the first of which can be proven by assuming q then applying the right intro rule for ∨ using
the assumed proof of p. The final implication can be proven in the same way using the left intro
rule for ∨ and an assumed proof of q.
QED.
-/
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume porq,
    apply or.elim porq _ _,
    assume p,
    apply or.intro_right _ _,
    apply p,
    assume q,
    apply or.intro_left _ _,
    apply q,
  -- backward
    assume qorp,
    apply or.elim qorp _ _,
    assume q,
    apply or.intro_right _ _,
    apply q,
    assume p,
    apply or.intro_left _ _,
    apply p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
/-
Apply the intro rule for ∀ by assuming arbirary propositions P and Q. Then apply the
intro rule for ↔ to create two implications as the new proof goal. Prove the first
implication by assuming a proof of P ∧ Q and applying the ∧ elimination rule to P ∧ Q.
Then assume P and then assume Q and apply the ∧ intro rule to prove the implication.
The other implication can be proved by assuming a proof of Q ∧ P and apply the ∧ elimation
rule to Q ∧ P. Finally assume a proof of Q and a proof of P and apply the ∧ intro rule
to proofs of Q and P to prove the implication, and therefore the overall assertion.
QED.
-/
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume pandq,
    apply and.elim pandq,
    assume p,
    assume q,
    apply and.intro q p,
  -- backward
    assume qandp,
    apply and.elim qandp,
    assume q,
    assume p,
    apply and.intro p q,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
/- 
Apply the introduction rule for ∀ by assuming arbitrary propositions
P, Q, and R. Then apply the introduction rule for ↔, creating two implications
that need to be proved. The forward implication is proven by assuming P ∧ (Q ∨ R),
and applying the ∧ elimination rule to that proof, creating a chain of implications,
which can be proven by assuming P and Q ∨ R and then applying the ∨ elimination rule
to Q ∨ R, creating two new implication to be proved, the first of which can be proved
by assuming Q and applying the left intro rule for or to make the new proof goal for that
implication P ∧ Q, which can be proved by applying the ∧ intro rule to the assumed proofs
of P and Q. The second implication can be proved by assuming a proof of R and using the right
intro rule for ∨ to make the new implication proof goal P ∧ R, which can be proved by using the ∧
intro rule with assumed proofs of P and R. Next the backwards direction of the implication must be
proved, which can be done by assuming P ∧ Q ∨ P ∧ R and then applying the ∨ elimination rule to that.
Now the proof goal is divided into two implications, the left and the right. The left implication can
be proven by assuming a proof of P ∧ Q and applying the ∧ intro rule to 
-/
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume pandqorr,
    apply and.elim pandqorr,
    assume p,
    assume qorr,
    apply or.elim qorr _ _,
    assume q,
    apply or.intro_left _ _,
    apply and.intro p q,
    assume r,
    apply or.intro_right _ _,
    apply and.intro p r,
  -- backward
    assume pandqorpandr,
    apply or.elim pandqorpandr,
    -- left
      assume pandq,
      apply and.intro _ _,
      apply and.elim pandq,
      assume p,
      assume q,
      apply p,
      apply or.intro_left,
      apply and.elim pandq,
      assume q,
      assume q,
      apply q,
    -- right
      assume pandr,
      apply and.intro _ _,
      apply and.elim pandr,
      assume p,
      assume r,
      apply p,
      apply or.intro_right,
      apply and.elim pandr,
      assume p,
      assume r,
      apply r,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume porqandr,
    apply and.intro,
    -- left
      apply or.elim porqandr _ _,
      assume p,
      apply or.intro_left _ _,
      apply p,
      assume qandr,
      apply or.intro_right _ _,
      apply and.elim qandr,
      assume q,
      assume r,
      apply q,
    -- right
      apply or.elim porqandr _ _,
      assume p,
      apply or.intro_left,
      apply p,
      assume qandr,
      apply or.intro_right,
      apply and.elim qandr,
      assume q,
      assume r,
      apply r,
  -- backward
   assume porqandporr,
   cases porqandporr,
   cases porqandporr_right,
   apply or.intro_left,
   apply porqandporr_right,
   cases porqandporr_left,
   apply or.intro_left,
   apply porqandporr_left,
   apply or.intro_right,
   apply and.intro porqandporr_left porqandporr_right,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
/-
Apply the introduction rule for ∀ by assuming arbitrary propositions
P and Q. Then apply the introduction rule for ↔ to create two implications
as a proof goal. The first implication cane be proven by assuming a proof of
P ∧ (P ∨ Q) and then applying the ∧ elimination rule to that proof. The
backwards implication can be proven by assuming a proof of P and applying
the intro rule for ∧ to create a proof goal of P and P ∨ Q. A proof of P 
can be provided by applying the assumed proof of P and then a proof of P ∨ Q can
be provided by using the left intro rule for ∨ and applying the assumed proof of P.
QED.
-/
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume pandporq,
    apply and.elim_left pandporq,
  -- backward
    assume p,
    apply and.intro _ _,
    apply p,
    apply or.intro_left _ _,
    apply p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
/-
Apply the intro rule for ∀ by assuming the arbitrary propositions
P and Q. Then apply the intro rule for ↔ to create two implications as
the proof goals. The first goal can be proved by assuming a proof of
P ∨ P ∧ Q and then applying the ∨ elimination rule to that assumed proof
to create two more implications to be proven. The first new implication can
be proven by assuming a proof of P and then applying that proof. The second
can be proved by assuming P ∧ Q and applying the left elimination rule of ∧
to it. The backwards implication can be proven by assuming P and applying
the ∨ left intro rule to the proof goal, P ∨ P ∧ Q, and then applying the assumed
proof of P.
QED.
-/
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume porpandq,
    apply or.elim porpandq _ _,
    -- left
      assume p,
      apply p,
    -- right
      assume pandq,
      apply and.elim_left pandq,
  -- backward
    assume p,
    apply or.intro_left,
    apply p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
/-
Apply the ∀ intro rule by assuming an arbitrary proposition, P. Then
apply the ↔ intro rule to create two implications as the new proof goal.
The forward implication can be proven by assuming a proof of P ∨ true and
then applying the intro rule for true. The backwards implication can be proven
by assuming true and applying the right intro rule for ∨ then applying the intro
rule for true.
QED.
-/
begin
  assume P,
  apply iff.intro,
  -- forward
    assume portrue,
    apply true.intro,
  -- backward
    assume t,
    apply or.intro_right,
    apply true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
/-
Apply the intro rule for ∀ by assuming an arbitray proposition P.
Then apply the intro rule for ↔ to create two implications as the
proof goal. The forward implication can be proved by assuming
P ∨ false and then doing a case analysis on it and showing that
P implies P and that a proof of false allows P to be proven. 
The backward implication can be proven by assuming P and then applying
the left intro rule for ∨ to the proof goal such that an application of
P proves the overall statement. 
QED.
-/
begin
  assume P,
  apply iff.intro,
  -- forward
    assume porfalse,
    cases porfalse,
    apply porfalse,
    cases porfalse,
  -- backward
    assume p,
    apply or.intro_left _ _,
    apply p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
/-
Apply the intro rule ∀ by assuming an arbitrary proposition P.
Then apply the intro rule for ↔. The first implication can be proven
by assuming P ∧ true and applying the left elimination rule to that
proof. The second implication can be proven by assuming P and then
applying the and intro rule such that only the intro rule for true must
be applied to prove the overall assertion.
-/
begin
  assume P,
  apply iff.intro,
  assume pandtrue,
  apply and.elim_left pandtrue,
  assume p,
  apply and.intro p,
  apply true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
/-
Apply the intro rule for ∀ by assuming an arbitrary proposition
P, then apply the ↔ intro rule. The first implication generated by
the ↔ intro rule can be proven by assuming P ∧ false and the using
the right elimination rule for ∧ to that proof. The second implication
can be proven by assuming false and applying and.intro to the proof goal
so that it is now P and false. Apply the elimination rule for false and the
proof of false to prove the overall proposition.
QED.
-/
begin
  assume P,
  apply iff.intro,
  assume pandfalse,
  apply and.elim_right pandfalse,
  assume f,
  apply and.intro,
  apply false.elim f,
  apply f,
end


