def pt (a b c : ℕ) : Prop := a * a + b * b = c * c

example : pt 3 4 5 :=
  begin
    unfold pt,
    apply eq.refl,
  end

example : pt 3 4 6 :=
  begin
    unfold pt,
    apply eq.refl,
  end


