import Mathlib.Data.Set.Basic

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  exact h.right
  -- simp at h
  -- exact h.right

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x h
  exact h.left

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact And.intro h1 h2

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h
  apply And.intro
  exact h1 h
  exact h2 h

theorem inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x h
  apply And.intro
  exact h.right
  exact h.left

theorem inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  exact inter_subset_swap A B
  exact inter_subset_swap B A

theorem inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro
  { intro ⟨⟨hA, hB⟩, hC⟩
    exact And.intro hA (And.intro hB hC) }
  { intro ⟨hA, ⟨hB, hC⟩⟩
    exact And.intro (And.intro hA hB) hC }
