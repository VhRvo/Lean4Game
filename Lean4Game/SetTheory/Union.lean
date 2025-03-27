import Mathlib.Data.Set.Basic

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (A B : Set U) : B ⊆ A ∪ B := by
  intro x h
  -- rewrite [Set.mem_union x A B]
  exact Or.inr h

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x h3
  rcases h3 with h | h
  { exact h1 h }
  { exact h2 h }

theorem union_subset_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x h
  rcases h with h1 | h1
  { exact Or.inr h1 }
  { exact Or.inl h1 }

theorem union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply Set.Subset.antisymm
  exact union_subset_swap A B
  exact union_subset_swap B A

theorem union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  apply Iff.intro
  { intro h
    rcases h with hAB | hC
    { rcases hAB with hA | hB
      { exact Or.inl hA }
      { exact Or.inr (Or.inl hB) } }
    { exact Or.inr (Or.inr hC) } }
  { intro h
    rcases h with hA | hBC
    { exact Or.inl (Or.inl hA) }
    { rcases hBC with hB | hC
      { exact Or.inl (Or.inr hB) }
      { exact Or.inr hC } } }
