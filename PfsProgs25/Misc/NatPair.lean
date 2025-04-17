/-
⊢ {α : Sort u} → (α → α → Prop) → Sort u
-/
#check Quot

/-
Quotient.{u} {α : Sort u} (s : Setoid α) : Sort u
-/
#check Quotient

/-
class Setoid.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Setoid.r : α → α → Prop
  Setoid.iseqv : Equivalence Setoid.r
constructor:
  Setoid.mk.{u} {α : Sort u} (r : α → α → Prop) (iseqv : Equivalence r) : Setoid α
-/
#print Setoid

abbrev NatPair := Quot (α := Nat × Nat)
    (fun (a, b) (c, d) => a = d && b = c)

def smaller : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then a else b)
  (by
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )


def larger : NatPair → Nat :=
  Quot.lift (fun (a, b) => if a < b then b else a)
  (by
    intro (a, b) (c, d)
    simp
    intro h₁ h₂
    rw [← h₁, ← h₂]
    if h: a < b then
      simp [h]
      have h' : ¬ b <a := by
        simp [Nat.le_of_lt, h]
      simp [h']
    else
      simp [h]
      if h': b < a then
        simp [h']
      else
        simp [h']
        cases Nat.lt_trichotomy a b
        case inl hlt =>
          simp [hlt] at h
        case inr hge =>
          cases hge
          case inl heq =>
            simp [heq]
          case inr hgt =>
            simp [hgt] at h'
    )

abbrev NatPair.mk (a b : Nat) : NatPair :=
  Quot.mk (α := Nat × Nat) (fun (a, b) (c, d) => a = d && b = c) ((a, b) : Nat × Nat)

theorem smaller_le_larger (a b : Nat):
  smaller (NatPair.mk a b) ≤
    larger (NatPair.mk a b) :=
  by
    rw [NatPair.mk, smaller, larger]
    simp only
    if h:a < b then
      simp [h]
      exact Nat.le_of_lt h
    else
      simp [h]
      exact Nat.le_of_not_gt h

#check Quot.ind

def List.size (l : List α) : Nat :=
  List.foldl (fun acc _ => acc + 1) 0 l

#eval [1, 2, 3].size

class inductive Algo where
| smart | stupid

def List.mySize {α} (l : List α)(algo: Algo := .smart) : Nat :=
  match algo with
  | .smart => List.size l
  | .stupid =>
     l.length

#eval [1, 2, 3].mySize

def List.myComplexSize {α} (l : List α)[algo: Algo] : Nat :=
  l.mySize algo

instance : Algo := .smart
#eval [1, 2, 3].myComplexSize
