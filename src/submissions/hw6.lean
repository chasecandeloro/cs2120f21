import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ {α : Type} (L : set α), L ∩ L = L :=
begin
  intros α L,
  apply set.ext,
  assume x,
  split,
  -- 1
    assume xL,
    cases xL,
    apply xL_left,
  -- 2
    assume xL,
    split,
    -- 1
      apply xL,
    -- 2
      apply xL,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ {α : Type} (L : set α) (H : set α), L ∪ H = H ∪ L :=
begin
  intros α L H,
  apply set.ext,
  assume x,
  apply iff.intro,
  -- 1
    assume xLH,
    cases xLH,
    -- 1
      apply or.intro_right,
      apply xLH,
    -- 2
      apply or.intro_left,
      apply xLH,
  -- 2
    assume xHL,
    cases xHL,
    -- 1
      apply or.intro_right,
      apply xHL,
    -- 2
      apply or.intro_left,
      apply xHL,
end
/-
The union of two sets is the set of every element in the sets, thus
the set of all elements in the first set and the second set is the same
for all elements in second set and the first set. The same set, containing
the same elements is created no matter the order.
QED.
-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example : ∀ {α : Type} (L M N : set α), (L ⊆ L) ∧ (L ⊆ M → M ⊆ N → L ⊆ N) :=
begin
  intros α L M N,
  apply and.intro,
  -- 1
    refl,
  -- 2
    assume LM,
    assume MN,
    show (∀ α, α ∈ L → α ∈ N),
    assume a_1,
    assume a1L,
    have a1M:= LM a1L,
    apply MN a1M,
end

/-
A set, x, that is a subset of another set, y, contains only elements
that are in y. Thus it follows that y is a subset of itself because it contains
only elements that are in y. Therefore subset is a reflexive relation.
If a set x is a subset of y and y is a subset of z, x contains only elements
in y and y contains only elements in z. Thus it follows that x is a subset of
z because all of the elements in x are in both y and z. Therefore subset is
a transitive relation.
QED.
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example : ∀ {α : Type} (L M N : set α), (((L ∪ M) ∪ N) = (L ∪ (M ∪ N))) ∧ (((L ∩ M) ∩ N) = (L ∩ (M ∩ N))) :=
begin
  intros,
  apply and.intro,
  -- 1
    apply set.ext,
    intros,
    split,
    -- 1
      assume xLMN,
      cases xLMN,
      cases xLMN,
      apply or.intro_left,
      apply xLMN,
      apply or.intro_right,
      apply or.intro_left,
      apply xLMN,
      apply or.intro_right,
      apply or.intro_right,
      apply xLMN,
    -- 2
      assume xLMN,
      cases xLMN,
      apply or.intro_left,
      apply or.intro_left,
      apply xLMN,
      cases xLMN,
      apply or.intro_left,
      apply or.intro_right,
      apply xLMN,
      apply or.intro_right,
      apply xLMN,
  -- 2
    apply set.ext,
    intros,
    split,
    -- 1
      assume xLMN,
      cases xLMN,
      cases xLMN_left,
      apply and.intro,
      -- 1
        apply xLMN_left_left,
      -- 2
        apply and.intro,
        -- 1
          apply xLMN_left_right,
        -- 2
          apply xLMN_right,
    -- 2
      assume xLMN,
      cases xLMN,
      cases xLMN_right,
      apply and.intro,
      -- 1
        apply and.intro,
          -- 1
            apply xLMN_left,
          -- 2
            apply xLMN_right_left,
      -- 2
        apply xLMN_right_right,
    
        
end

/-
The union of two sets is the set of all elements in either set. If x y and z
are sets the union of them is the set of all elements in x y and z. Because the
union relation between two sets is always the same set (it is communative), the
union of any number of sets, no matter the order taken is always the same set.
Thus the union relation is associative. The intersection of two sets is the
set of elements shared between the two sets. The intersection of three sets
is the set of elements present in all three sets. Because the intersection
relation always generates this set of shared elements when given three sets,
it does not matter the order in which the sets are proved. Thus the intersection
relation is associative.
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example : ∀ {α : Type} (L M R : set α), L ∩ (M ∩ R) = (L ∩ M) ∩ (L ∩ R) :=
begin
  intros,
  apply set.ext,
  intros,
  split,
  -- 1
    assume xLMR,
    cases xLMR,
    cases xLMR_right,
    apply and.intro,
    -- 1
      apply and.intro,
      -- 1
        apply xLMR_left,
      -- 2
        apply xLMR_right_left,
    -- 2
      apply and.intro,
      -- 1
        apply xLMR_left,
      -- 2
        apply xLMR_right_right,
  -- 2
    assume xLMLR,
    cases xLMLR,
    cases xLMLR_right,
    cases xLMLR_left,
    apply and.intro,
    -- 1
      apply xLMLR_left_left,
    -- 2
      apply and.intro,
      -- 1
        apply xLMLR_left_right,
      -- 2
        apply xLMLR_right_right,
end

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ {α : Type} (L M R : set α), L ∪ (M ∩ R) = (L ∪ M) ∩ (L ∪ R) :=
begin
  intros,
  apply set.ext,
  intros,
  split,
  -- 1
    assume xLMR,
    cases xLMR,
    -- 1
      apply and.intro,
      -- 1
        apply or.intro_left,
        apply xLMR,
      -- 2
        apply or.intro_left,
        apply xLMR,
    -- 2
      cases xLMR,
      apply and.intro,
      -- 1
        apply or.intro_right,
        apply xLMR_left,
      -- 2
        apply or.intro_right,
        apply xLMR_right,
  -- 2
    assume xLMLR,
    cases xLMLR,
    cases xLMLR_left,
    cases xLMLR_right,
    -- 1
      apply or.intro_left,
      apply xLMLR_left,
    -- 2
      apply or.intro_left,
      apply xLMLR_left,
    -- 3
      cases xLMLR_right,
      -- 1
        apply or.intro_left,
        apply xLMLR_right,
      -- 2
        apply or.intro_right,
        apply and.intro,
        -- 1
          apply xLMLR_left,
        -- 2
          apply xLMLR_right,
end