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
  -- h: ¬(0=0)
  -- h: (0=0) → false
  apply false.elim(h (eq.refl 0)),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  -- ¬¬P
  
  assume h,
  apply false.elim(h p),
end



-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  -- left
    exact p,
  -- right
    contradiction,
end