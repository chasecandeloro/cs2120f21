-- My Lecture14.lean

axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=
  begin
    apply iff.intro,
    -- forward
      assume all,
      have f := classical.em (∃ (p : Person), ¬Likes p p),
      cases f,
      -- 1
        apply f,
      -- 2
        have contra : ∀ (p : Person), Likes p p := _, 
        contradiction,
        -- 1
          assume p,
          have g := classical.em (Likes p p),
          cases g,
          -- 1
            assumption,
          -- 2
            have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
            contradiction,
    -- backward
      assume ex,
      cases ex with p l,  
      
    
  end 