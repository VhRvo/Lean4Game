import Mathlib.Data.Set.Basic

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h
  exact h2 (h h1)

theorem mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rewrite [mem_compl_iff A x]
  rewrite [mem_compl_iff] at h2
  -- by_contra h
  intro h
  exact h2 (h1 h)

-- theorem Subset.antisymm {A B : Set U} : A ⊆ B → B ⊆ A → A = B := sorry

theorem compl_compl₀ (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  { intro x h
    rewrite [mem_compl_iff] at h
    rewrite [mem_compl_iff] at h
    push_neg at h
    exact h }
  { intro x h
    rewrite [mem_compl_iff]
    by_contra h1
    exact h1 h }

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  { intro h
    exact compl_subset_compl_of_subset h }
  { intro h x h1
    by_contra h2
    exact h h2 h1 }
