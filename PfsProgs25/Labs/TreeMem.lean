import Mathlib

namespace lab

/-
class Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
number of parameters: 2
fields:
  Membership.mem : γ → α → Prop
constructor:
  Membership.mk.{u, v} {α : outParam (Type u)} {γ : Type v} (mem : γ → α → Prop) : Membership α γ
-/
#print Membership

inductive BinTree (α : Type) where
  | leaf (label: α) : BinTree α
  | node : BinTree α → BinTree α → BinTree α
deriving Inhabited, Repr

def BinTree.toList {α : Type} : BinTree α → List α
  | leaf a => [a]
  | node t₁ t₂ => toList t₁ ++ toList t₂

/-!
## Membership class

The membership typeclass represents belonging to sets, lists and other collections. The notation `x ∈ y` makes sense if `x: α`, `y: β` and there is an instance of `Membership α β`

1. Define an instance of Membership in `BinTree α` corresponding to being a label. You may want to define an auxiliary function (or inductive type) first. (3 marks)
-/
def BinTree.containsLabel {α : Type} : (BinTree α) → α → Prop
  | leaf a => fun label ↦ (label = a)
  | node t₁ t₂ => fun label ↦ (containsLabel t₁ label) ∨ (containsLabel t₂ label)

instance {α: Type} : Membership α (BinTree α) := Membership.mk BinTree.containsLabel

/-!
2. Prove that membership in a tree is equivalent to that in the corresponding list (3 marks).
-/
theorem in_iff_containsLabel {α: Type} (tree : BinTree α) :
  ∀ x: α, x ∈ tree ↔ tree.containsLabel x := by
    intro x
    simp [Membership.mem]

theorem mem_tree_iff_mem_list {α : Type} (tree : BinTree α) :
  ∀ elem : α, elem ∈ tree ↔ elem ∈ tree.toList := by
  intro elem
  induction tree with
  | leaf value =>
    rw [in_iff_containsLabel]
    unfold BinTree.containsLabel
    unfold BinTree.toList
    simp
  | node left right ih_left ih_right =>
    constructor
    · intro h
      rw [in_iff_containsLabel] at h
      unfold BinTree.containsLabel at h
      unfold BinTree.toList
      simp
      cases h with
      | inl hl =>
        left
        rw [← in_iff_containsLabel, ih_left] at hl
        assumption
      | inr hr =>
        right
        rw [← in_iff_containsLabel, ih_right] at hr
        assumption
    · intro h
      rw [in_iff_containsLabel]
      unfold BinTree.containsLabel
      unfold BinTree.toList at h
      simp at h
      cases h with
      | inl hl =>
        left
        rw [← in_iff_containsLabel, ih_left]
        assumption
      | inr hr =>
        right
        rw [← in_iff_containsLabel, ih_right]
        assumption


/-!
## Decidability

Having a decision procedure for (families of) propositions is captured by the `Decidable` typeclass. A term of `Decidable p` is either a proof that decidable is true or that it is false.
-/

/-
inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#print Decidable

/-!
3. Using that membership in a List of natural numbers is decidable (or in some other way), construct an instance of the following. Note that a convenient way to use a decidable property is with an `if` statement of the form `if c:property then ... else ...`. (3 marks)
-/
instance {x: Nat} {t: BinTree Nat} : Decidable (x ∈ t) := by
  if h: x ∈ t.toList
  then
    rw [← mem_tree_iff_mem_list] at h
    apply Decidable.isTrue h
  else
    rw [← mem_tree_iff_mem_list] at h
    apply Decidable.isFalse h

/-!
As a test, uncomment the eval statements to get the appropriate results
-/
open BinTree in
def eg₁ := node (node (leaf 3) (leaf 4)) (leaf 3)

#eval 3 ∈ eg₁

#eval 7 ∈ eg₁

end lab
