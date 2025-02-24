import Mathlib

structure Half (n : Nat) where
  val : Nat
  isHalf : val + val = n
deriving Repr

/-
inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α
-/
#print Option

def half? (n : Nat): Option (Half n) :=
    match n with
    | 0 => Option.some { val := 0, isHalf := by simp }
    | 1 => Option.none
    | k + 2 =>
      let h? := half? k
      h?.map fun ⟨m, p⟩  => by
        use m + 1
        rw [← p]
        omega

/-
some { val := 0, isHalf := _ }
-/
#eval half? 0

/-
some { val := 5, isHalf := _ }
-/
#eval half? 10

#eval half? 13 -- none

/-!
Option is a monad. We can use do notation to simplify the code.
-/
def OneAndAHalf (n : Nat) : Option Nat := do
  let ⟨m, _⟩ ← half? n
  return 3 * m

def quarter (n : Nat) : Option Nat := do
  let ⟨m, _⟩ ← half? n
  let ⟨k, _⟩ ← half? m
  return k

/-
structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
number of parameters: 2
fields:
  Subtype.val : α
  Subtype.property : p ↑self
constructor:
  Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p
-/
#print Subtype

def quarterWithProof (n : Nat) :
    Option {k: Nat // k + k + k + k = n}  := do
  let ⟨m, p₁⟩ ← half? n
  let ⟨k, p₂⟩ ← half? m
  return ⟨k, by
    rw [← p₁, ← p₂]
    omega⟩

#eval quarterWithProof 16 -- some 4

def half?' (n? : Option Nat) : Option Nat := do
  let n ← n?
  let ⟨m, _⟩ ← half? n
  return m

def half! (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => panic! "odd number"
  | k + 2 =>
    let m := half! k
    m + 1

#eval half! 10 -- 5

-- #eval half! 11
