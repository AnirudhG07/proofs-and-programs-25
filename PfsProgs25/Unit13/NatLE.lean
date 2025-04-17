import Lean
import PfsProgs25.Unit13.MetaSolve
open Lean Meta Elab Term Tactic

/-!
# Transitivity for `LE` on `Nat`

We *rewrite* inequalities for natural numbers using transitivity. Namely, if the goal is `a ≤ b` and we have `a ≤ c`, we can rewrite the goal to `c ≤ b` and similarly for `c ≤ b` and for just `a ≤ b`.
-/
/-
Nat.le_trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k
-/
#check Nat.le_trans

/-
natLeExpr? (e : Expr) : MetaM (Option (Expr × Expr))
-/
#check natLeExpr?

elab "nat_le_trans" t:term : tactic =>
  withMainContext do
    match ← natLeExpr? <| ← getMainTarget with
    | none => throwError "Goal not an LE expression"
    | some (a, b) =>
      let h ← Tactic.elabTerm t none
      match ← natLeExpr? <| ← inferType h with
      | none => throwError "Hypothesis not an LE expression"
      | some (c, d) =>
        let checkLeft ← isDefEq a c
        let checkRight ← isDefEq b d
        if checkLeft && checkRight then
          closeMainGoal `nat_le_trans  h
        else
          if checkLeft then
            -- the new goal is `d ≤ b` and
            -- the original goal follows from `h` and the new goal
            let newGoalType ← mkAppM ``Nat.le #[d, b]
            let newGoal ← mkFreshExprMVar newGoalType
            let goal ← getMainGoal
            let pf ← mkAppM ``Nat.le_trans #[h, newGoal]
            goal.assign pf
            replaceMainGoal [newGoal.mvarId!]
          else if checkRight then
            -- the new goal is `a ≤ c` and
            -- the original goal follows from `h` and the new goal
            let newGoalType ← mkAppM ``Nat.le #[a, c]
            let newGoal ← mkFreshExprMVar newGoalType
            let goal ← getMainGoal
            let pf ← mkAppM ``Nat.le_trans #[newGoal, h]
            goal.assign pf
            replaceMainGoal [newGoal.mvarId!]
          else
            throwError "Could not rewrite as neither ends match"

example (a: Nat)(h : a ≤ 3): a ≤ 4 := by
  nat_le_trans h
  simp


example (a: Nat)(h : 2 ≤ a): 0 ≤ a := by
  nat_le_trans h
  simp
