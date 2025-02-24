import Mathlib

/-!
## Vectors as indexed inductive types

There are two common ways to define vectors in Lean, as indexed inductive types or as structures. In Lean, Vectors are defined as structures. Here, we define vectors as indexed inductive types.
-/
inductive Vec (α : Type u): Nat → Type u where
  | nil : Vec α  0
  | cons {n : Nat} (a : α) (v : Vec (α := α) n) : Vec α  (n + 1)

def Vec.add [Add α] : {n : Nat} → Vec α n → Vec α n → Vec α n
  | 0,   _ ,     _       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)
