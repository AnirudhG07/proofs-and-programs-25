import Std
/-!
## Fibonacci numbers: memoization using the state monad

The naive way of computing Fibonacci numbers is very inefficient because it recomputes the same values many times. We can use the state monad to store the values of the Fibonacci numbers we have already computed. This is a simple example of memoization.

We will also take a more complicated example: Catalan numbers. The Catalan numbers are a sequence of natural numbers that occur in various counting problems, often involving recursively defined objects. They satisfy the recurrence relation:
* $C_0 = 1`,
* $C_n = \sum_{i=1}^n C_{i-1} C_{n-i}$, for $n \geq 0.$
-/
open Std
#check HashMap
#check StateM
#check modify

abbrev FibState := HashMap Nat Nat
abbrev FibM := StateM FibState

def fib (n: Nat) : FibM Nat := do
  match n with
  | 0 => return 1
  | 1 => return 1
  | k + 2 => do
    let m ← get
    match m.get? n with -- check if we calculated it before
    | some v => return v
    | none => do
      let v1 ← fib k
      let v2 ← fib (k + 1)
      let v := v1 + v2
      modify (fun m => m.insert n v)
      return v

#check fib 350

/-
StateT.run'.{u, v} {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α
-/
#check StateT.run'

-- `run` calculates given an initial state and returns the result and the final state
-- `run'` calculates given an initial state and returns the result
#eval fib 350 |>.run' {}

/-
(233,
 Std.HashMap.ofList [(12, 233),
  (11, 144),
  (10, 89),
  (9, 55),
  (8, 34),
  (7, 21),
  (6, 13),
  (5, 8),
  (4, 5),
  (3, 3),
  (2, 2)])
-/
#eval fib 12 |>.run {}

/-
(144,
 Std.HashMap.ofList [(12, 144),
  (11, 89),
  (10, 55),
  (9, 34),
  (8, 21),
  (7, 13),
  (6, 8),
  (5, 5),
  (4, 3),
  (3, 2),
  (2, 1),
  (1, 1),
  (0, 1)])
-/
#eval fib 12 |>.run (HashMap.ofList [(0, 1), (1, 1), (2, 1)])

#eval fib 12 |>.run (HashMap.ofList [(0, 19)])

/-!
## Catalan numbers
-/
namespace Catalan
abbrev CatState := HashMap Lean.Name <| HashMap Nat Nat
abbrev CatM := StateM CatState

partial def cat (n: Nat) : CatM Nat := do
  match n with
  | 0 => return 1
  | k + 1 => do
    let m ← get
    let m?' := m.get? `cat
    match m?'.bind <| fun m' =>  m'.get? n with
    | some v => return v
    | none => do
      let mut sum := 0
      for i in [0:k+1] do
        let v1 ← cat i
        let v2 ← cat (k - i)
        sum := sum + v1 * v2
      modify (fun m =>
          let m' := m.getD `cat HashMap.empty
          m.insert `cat <| m'.insert n sum)
      -- set .. -- correct but not optimized
      return sum

#eval cat 100 |>.run' {}
end Catalan

namespace CatalanSimple
abbrev CatState := HashMap Nat Nat
abbrev CatM := StateM CatState

partial def cat (n: Nat) : CatM Nat := do
  match n with
  | 0 => return 1
  | k + 1 => do
    let m ← get
    match m.get? n with
    | some v => return v
    | none => do
      let mut sum := 0
      for i in [0:k+1] do
        let v1 ← cat i
        let v2 ← cat (k - i)
        sum := sum + v1 * v2
      modify (fun m => m.insert n sum)
      -- set m.insert n sum -- correct but not optimized
      return sum

#eval cat 100 |>.run' {}

end CatalanSimple
