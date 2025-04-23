

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

theorem disjoint
  {inst : DecidableEq Inhabitant}
  {left : Finset Inhabitant}
  {right : Finset Inhabitant}
  (h : left ∩ right = ∅)
  (Aleft : A ∈ left)
  (Aright : A ∈ right) : False := by
  have A_in_empty : A ∈ left ∩ right:= Finset.mem_inter.mpr (And.intro Aleft Aright)
  rw [h] at A_in_empty
  exact Finset.not_mem_empty A A_in_empty

theorem disjoint₁
  {inst : DecidableEq Inhabitant}
  {left : Finset Inhabitant}
  {right : Finset Inhabitant}
  (Aleft : A ∈ left)
  (Aright : A ∈ right)
  (h : left ∩ right = ∅)
  (A_not_in_Empty : A ∉ (∅ : Finset Inhabitant)) : False := by
  have A_in_empty : A ∈ left ∩ right:= Finset.mem_inter.mpr (And.intro Aleft Aright)
  rw [h] at A_in_empty
  exact A_not_in_Empty A_in_empty

theorem inleft_notinright
  {left : Finset K}
  {right : Finset K}
  {inst : DecidableEq K}
  (h : left ∩ right = ∅)
  (Aleft : A ∈ left) : A ∉ right := by
  intro Aright
  have h1 := disjoint h Aleft Aright
  exact h1

example
  {A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant}
  {Knave : Finset Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  (AKnight : A ∈ Knight)
  : A ∉ Knave := by
  intro AKnave
  exact disjoint h AKnight AKnave

theorem inright_notinleft
  {left : Finset K}
  {right : Finset K}
  {inst : DecidableEq K}
  (h : left ∩ right = ∅ )
  (Aright : A ∈ right)
  : A ∉ left := by
  intro Aleft
  exact disjoint h Aleft Aright

example
  {inst : DecidableEq K}
  {Knight : Finset K}
  {Knave : Finset K}
  (h : Knight ∩ Knave = ∅ )
  (h' : A ∈ Knave)
  : ¬ (A ∈ Knight)
  := by
  intro h1
  exact disjoint h h1 h'

example
  {_inst : DecidableEq K}
  {Knight : Finset K}
  {Knave : Finset K}
  {_h : Knight ∩ Knave = ∅ }
  {Or : A ∈ Knight ∨ A ∈ Knave}
  {h' : ¬ (A ∈ Knight)}
  : A ∈ Knave
  := by
  cases Or with
  | inl AKnight => exact (h' AKnight).elim
  | inr AKnave => exact AKnave

example
  {Knight : Finset Inhabitant }
  {Knave : Finset Inhabitant}
  {_inst : DecidableEq Inhabitant}
  (h' : ¬ (A ∈ Knave))
  (h'' : A ∈ Knight ∨ A ∈ Knave)
  : A ∈ Knight
  := by
  cases h'' with
  | inl AKnight => exact AKnight
  | inr AKnave => exact (h' AKnave).elim

-- A says 'I am a knave'
-- A ∈ Knight → A ∈ Knave
-- A ∈ Knave → A ∈ Knight
-- A ∈ Knave → ¬(A ∈ Knave)
-- ¬(A ∈ Knave) → A ∈ Knave

theorem IAmKnave
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant}
  {Knave : Finset Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  {h1 : A ∈ Knight ∨ A ∈ Knave}
  {stA : A ∈ Knight ↔ A ∈ Knave}
  {stAn : A ∈ Knave ↔ ¬ (A ∈ Knave)}
  : False
  := by
  cases h1 with
  | inl AKnight =>
  { have AKnave := stA.mp AKnight
    exact disjoint h AKnight AKnave }
  | inr AKnave =>
  { have ANKnave := stAn.mp AKnave
    exact ANKnave AKnave }
