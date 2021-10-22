import data.set

def evens : set ℕ := { n | n % 2 = 0}

example : ({0, 2} : set ℕ) ⊆ evens :=
begin
  show (∀ n, n = 0 ∨ n = 2 → n ∈ evens),
  assume n,
  assume n0or2,
  cases n0or2,
  -- 1
    rw n0or2,
    unfold evens,
    show {n : ℕ | n % 2 = 0} 0,
    show 0 % 2 = 0,
    apply eq.refl,
  -- 2
    rw n0or2,
    unfold evens,
    show {n : ℕ | n % 2 = 0} 2,
    show 2 % 2 = 0,
    apply eq.refl,
end