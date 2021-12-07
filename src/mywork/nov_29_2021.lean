import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type
| zero : nat
| succ (n' : nat) : nat

def z := nat.zero
def o := nat.succ z
def t := nat.succ o

#check t
#reduce t

def f : nat :=
begin
  exact nat.succ (nat.succ t),
end

def inc' : nat → nat :=
begin
  assume n,
  exact nat.succ n,
end

#reduce inc' f

def inc : nat → nat
| n := nat.succ n

#reduce inc f

def dec : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := n'

def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)

#reduce mul t f
#reduce mul f f

def sum_to : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (nat.succ n')



theorem foo : ∀ (n : nat), P n 

theorem sum_up_to (n : nat)

end hidden

def P : nat → Prop
| n := 