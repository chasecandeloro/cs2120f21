-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  --forward
    assume notpandq,
    have pornotp:= classical.em P,
    have qornotq:= classical.em Q,
    cases pornotp,
    cases qornotq,
    -- 1
      apply or.intro_left,
      assume p,
      apply notpandq (and.intro p qornotq),
    -- 2
      apply or.intro_right,
      apply qornotq,
    -- 3
      apply or.intro_left,
      apply pornotp,
  --backward
    assume notpornotq,
    assume pandq,
    apply or.elim notpornotq,
      -- 1
        assume notp,
        apply notp (and.elim_left pandq),
      -- 2
        assume notq,
        apply notq (and.elim_right pandq),
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notpandq,
  apply and.intro,
  -- 1
    assume p,
    apply notpandq,
    apply or.intro_left,
    apply p,
  -- 2
    assume q,
    apply notpandq,
    apply or.intro_right,
    apply q,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
    assume P Q,
    apply iff.intro,
    -- forward
      assume pornotpandq,
      cases pornotpandq,
      -- 1
        apply or.intro_left,
        apply pornotpandq,
      -- 2
        apply or.intro_right,
        apply and.elim_right pornotpandq,
    -- backward
      assume porq,
      have pornotp := classical.em P,
      cases pornotp,
      -- 1
        apply or.intro_left,
        apply pornotp,
      -- 2
        cases porq,
        -- 1
          contradiction,
        -- 2
          apply or.intro_right,
          apply and.intro pornotp porq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume porqandporr,
    cases porqandporr,
    cases porqandporr_right,
    -- 1
      apply or.intro_left,
      apply porqandporr_right,
    -- 2
      cases porqandporr_left,
      -- 1
        apply or.intro_left,
        apply porqandporr_left,
      -- 2
        apply or.intro_right,
        apply and.intro porqandporr_left porqandporr_right,
  -- backward
    assume porqandr,
    apply and.intro,
    -- 1
      apply or.elim porqandr _ _,
      -- 1
        assume p,
        apply or.intro_left _ _,
        apply p,
      -- 2
        assume qandr,
        apply or.intro_right _ _,
        apply and.elim qandr,
        assume q,
        assume r,
        apply q,
    -- 2
      apply or.elim porqandr _ _,
      -- 1
        assume p,
        apply or.intro_left,
        apply p,
      -- 2
        assume qandr,
        apply or.intro_right,
        apply and.elim qandr,
        assume q,
        assume r,
        apply r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  -- forward
    assume porqandrors,
    cases porqandrors,
    cases porqandrors_left,
    cases porqandrors_right,
    -- 1
      apply or.intro_left,
      apply and.intro porqandrors_left porqandrors_right,
    -- 2
      apply or.intro_right,
      apply or.intro_left,
      apply and.intro porqandrors_left porqandrors_right,
    -- 3
      cases porqandrors_right,
        -- 1
          apply or.intro_right,
          apply or.intro_right,
          apply or.intro_left,
          apply and.intro porqandrors_left porqandrors_right,
        -- 2
          apply or.intro_right,
          apply or.intro_right,
          apply or.intro_right,
          apply and.intro porqandrors_left porqandrors_right,
  -- backward
    assume h,
    cases h,
    -- 1
      have p := and.elim_left h,
      have r := and.elim_right h,
      apply and.intro,
      -- 1
        apply or.intro_left,
        apply p,
      -- 2
        apply or.intro_left,
        apply r,
    -- 2
      cases h,
      -- 1
        have p := and.elim_left h,
        have s := and.elim_right h,
        apply and.intro,
        -- 1
          apply or.intro_left,
          apply p,
        -- 2
          apply or.intro_right,
          apply s,
      -- 2
        cases h,
        -- 1
          have q := and.elim_left h,
          have r := and.elim_right h,
          apply and.intro,
          -- 1
            apply or.intro_right,
            apply q,
          -- 2
            apply or.intro_left,
            apply r,
        -- 2
          have q := and.elim_left h,
          have s := and.elim_right h,
          apply and.intro,
          -- 1
            apply or.intro_right,
            apply q,
          -- 2
            apply or.intro_right,
            apply s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ ∀ (n : ℕ), n=0 :=
begin
  assume h,
  have g:= h 1,
  cases g,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  -- forward 
    assume pimpq,
    have pornotp:= classical.em P,
    apply or.elim pornotp,
    -- 1
      assume p,
      apply or.intro_right,
      apply pimpq p,
    -- 2
      assume notp,
      apply or.intro_left,
      apply notp,
  -- backward
    assume notporq,
    assume p,
    cases notporq,
     -- 1
     contradiction,
     apply notporq,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume notq,
  assume p,
  have q := pimpq p,
  contradiction,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume notpimpnotq,
  assume q,
  -- (P → false) → (Q → false) 
  have pornotp := classical.em P,
  cases pornotp,
  -- 1
    apply pornotp,
  -- 2
    have notq := notpimpnotq pornotp,
    contradiction,
end