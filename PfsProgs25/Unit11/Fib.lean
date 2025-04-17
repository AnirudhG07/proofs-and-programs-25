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
      let v1 ← fib k -- calculate at k and update the state
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

def cat (n: Nat) : CatM Nat := do
  match n with
  | 0 => return 1
  | k + 1 => do
    let m ← get
    let m?' := m.get? `cat
    match m?'.bind <| fun m' =>  m'.get? n with
    | some v => return v
    | none => do
      let mut sum := 0
      for p:i in [0:k+1] do
        have _ := p.upper
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

def cat (n: Nat) : CatM Nat := do
  match n with
  | 0 => return 1
  | k + 1 => do
    let m ← get
    match m.get? n with
    | some v => return v
    | none => do
      let mut sum := 0
      for p:i in [0:k+1] do
        have _ := p.upper
        let v1 ← cat i
        let v2 ← cat (k - i)
        sum := sum + v1 * v2
      modify (fun m => m.insert n sum)
      -- set m.insert n sum -- correct but not optimized
      return sum

#eval cat 100 |>.run' {}

end CatalanSimple

namespace CatalanOps

structure CatState where
  memo : HashMap Nat Nat := HashMap.empty
  natOps : Nat := 0
  count : Nat := 0
deriving Inhabited

instance : Repr CatState where
  reprPrec s _ := "Memo size: " ++ repr s.memo.size ++ ", " ++ "Operations: " ++ repr s.natOps ++ ", " ++ "Loops: " ++ repr s.count

abbrev CatM := StateM CatState

def addOps (n: Nat := 1) : CatM Unit := do
  modify (fun s => { s with natOps := s.natOps + n })

def withCount {α} (x : CatM α) : CatM α := do
  modify (fun s => { s with count := s.count + 1 })
  x

def cat (n: Nat) : CatM Nat := do
  match n with
  | 0 => return 1
  | k + 1 => do
    let m ← get
    match m.memo.get? n with
    | some v => return v
    | none => withCount do
      let mut sum := 0
      for p:i in [0:k+1] do
        have _ := p.upper
        let v1 ← cat i
        let v2 ← cat (k - i)
        sum := sum + v1 * v2
        addOps 3
      modify (fun m => { m with memo := m.memo.insert n sum })
      return sum

#eval cat 100 |>.run {}

end CatalanOps

structure  MyStateM (σ : Type) (α : Type) where
  run : σ → α × σ

namespace MyStateM

def pure {σ α : Type} (a : α) : MyStateM σ α :=
  {run := fun s => (a, s)}

def bind {σ α β : Type} (x : MyStateM σ α)
    (f : α → MyStateM σ β) : MyStateM σ β :=
  ⟨fun s => -- initial state
    let (a, s') := run x s -- value `a` and final state `s'`
    run (f a) s'
    ⟩

instance : Monad (MyStateM σ) where
  pure := pure
  bind := bind

def get {σ : Type} : MyStateM σ σ :=
  ⟨fun s => (s, s)⟩

def set {σ : Type} (s : σ) : MyStateM σ Unit :=
  ⟨fun _ => ((), s)⟩

def modify {σ : Type} (f : σ → σ) : MyStateM σ Unit :=
  ⟨fun s => ((), f s)⟩

def run' {σ α : Type} (x : MyStateM σ α) (s : σ) : α :=
  let (a, _) := x.run s
  a

end MyStateM

/-
def StateT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
fun σ m α ↦ σ → m (α × σ)
-/
#print StateT
