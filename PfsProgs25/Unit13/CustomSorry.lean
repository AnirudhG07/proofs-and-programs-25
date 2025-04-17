import Lean

open Lean Meta Elab Term Tactic

/-
sorryAx.{u} (α : Sort u) (synthetic : Bool := false) : α
-/
#check sorryAx

/-!
# Tactics

A tactic is a term of type `TacticM Unit`. So it returns nothing. However, it changes the *state* of the system.

## The `todo` tactic

The `todo` tactic is a simple tactic that logs a warning message with the string passed to it. It then replaces the main goal with a term built with `sorry`.
-/
/-
Lean.Elab.Tactic.getMainTarget : TacticM Expr
-/
#check getMainTarget

elab "todo" s:str : tactic =>
  withMainContext do
    let msg := s.getString
    logWarning m!"TODO: {msg}"
    let target ← getMainTarget
    let t ← mkAppM ``sorryAx #[target, mkConst ``false]
    closeMainGoal `todo t

example (n: Nat) : n = n := by
  todo "prove this"


def MyNames.myNat := 2

#eval `myNat

open MyNames in
#check ``myNat

/-!
# Metaprogramming in Lean

* A Lean program, term, command etc is given by a string.
* A `parser` converts this to syntax. A syntax can be of many types.
* The `elaborator` converts this to terms, commands or tactics in the internal foundations of lean.
-/
elab "#stx" "[" t:term "]" : command => do
  logInfo m!"Syntax: {t};\n{repr t}"

elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  let t ← reduce t
  let t ← instantiateMVars t
  logInfo m!"Reduced: {t}:\n{repr t}"

#stx [1 + 2]

#expr [(1 : Nat) + 2]

#expr [fun (n : Nat) ↦ (1 : Nat) + n]

#expr [fun (n m : Nat) ↦ (1 : Nat) + n]

#expr [(sorry : Nat)]

macro "scowl" s:str : tactic => do
  let msg := s.getString
  let msg := msg ++ "⌢"
  let m := Syntax.mkStrLit msg
  let n := Syntax.mkNatLit 3
  `(tactic|todo $m)

example : 1 = 1 := by
  scowl "you should do this."
