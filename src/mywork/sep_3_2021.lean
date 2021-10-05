/-
Theorem: Equality is symmetric
Proof :
For all types and two objects of a type, x
and y, assuming x equals y, substitute y for
x so that y equals y, which is true by 
reflexivity.
-/

theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x :=
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y),
    rw e,
  end 

/-
Proof: First we'll assume that T isa ny type
and we have objects x and y of this type. What
remains to show is that x = y 
-/

theorem eq_trans :
 ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
 begin
   assume (T : Type),
   assume (x y z : T),
   assume (e : x = y),
   assume (f : y = z),
   rw e,
   rw f,
 end