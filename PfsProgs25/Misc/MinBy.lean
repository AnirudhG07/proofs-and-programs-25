import Mathlib
def List.minBy? (l : List α) (f : α → Nat) : Option α :=
  match l with
  | [] => none
  | x :: xs =>
    match xs.minBy? f with
    | none => some x
    | some y =>
      if f x < f y then
        some x
      else
        some y

def List.minBy (l : List α) (f : α → Nat)(h: l ≠ []) : α :=
  match l with
  | x :: xs =>
    match p:xs with
    | [] => x
    | y :: ys =>
      let tailMin := List.minBy (y :: ys) f (by simp [p])
      if f x < f tailMin then
        x
      else
        tailMin

namespace List
theorem min_minBy (l : List α) (f : α → Nat)(h: l ≠ []):
  ∀ x ∈ l, f x ≥ f (List.minBy l f h) := by
  match p':l with
  | [] => contradiction
  | x :: xs =>
    match p:xs with
    | [] =>
      simp [minBy, p, p']
    | y :: ys =>
      simp [minBy, p, p']
      let ih := min_minBy (y :: ys) f (by simp [p])
      split
      · simp
        rename_i h
        apply And.intro
        · have h' := ih y (by simp [p])
          trans f (minBy (y :: ys) f (by simp [p]))
          · apply le_of_lt
            assumption
          · exact h'
        · intro a ah
          have h' := ih a (by simp [ah])
          trans f (minBy (y :: ys) f (by simp [p]))
          · apply le_of_lt
            assumption
          · exact h'
      · rename_i h''
        apply And.intro
        · apply le_of_not_gt
          exact h''
        · apply And.intro
          · apply ih y (by simp [p])
          · intro a ah
            apply ih a (by simp [ah])
end List
