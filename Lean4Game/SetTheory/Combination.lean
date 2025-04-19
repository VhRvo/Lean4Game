import Mathlib.Data.Set.Basic

theorem compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by

  apply Set.Subset.antisymm
  { intro x h
    apply And.intro
    { intro hA
      { exact h (Or.inl hA) } }
    { intro hB
      { exact h (Or.inr hB) } } }
  { intro x h hAB
    rcases hAB with hA | hB
    { exact h.left hA }
    { exact h.right hB } }

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  apply Iff.intro
  { intro h
    by_contra h1
    rewrite [←Set.mem_compl_iff] at h1
    rewrite [compl_union Aᶜ Bᶜ] at h1
    rewrite [compl_compl, compl_compl] at h1
    exact h h1 }
  { intro h hAB
    rcases h with hnA | hnB
    { exact hnA hAB.left }
    { exact hnB hAB.right } }

theorem compl_inter₁ (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [←compl_compl (Aᶜ ∪ Bᶜ)]
  rewrite [compl_union]
  rewrite [compl_compl, compl_compl]
  rfl

theorem inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro
  { intro ⟨ hA, hBC ⟩
    rcases hBC with hB | hC
    { exact Or.inl ⟨ hA, hB ⟩ }
    { exact Or.inr ⟨ hA, hC ⟩ } }
  { intro h
    rcases h with ⟨ hA, hB ⟩ | ⟨ hA, hC ⟩
    { exact ⟨ hA, Or.inl hB ⟩ }
    { exact ⟨ hA, Or.inr hC ⟩ } }

theorem union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro
  { intro h
    rcases h with hA | ⟨ hB, hC ⟩
    { exact ⟨ Or.inl hA, Or.inl hA ⟩ }
    { exact ⟨ Or.inr hB, Or.inr hC ⟩ } }
  { intro ⟨ hAB, hAC ⟩
    rcases hAB with hA | hB
    { exact Or.inl hA }
    { rcases hAC with hA | hC
      { exact Or.inl hA }
      { exact Or.inr ⟨ hB, hC ⟩ } } }

theorem union_distrib_left₀ (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rewrite [←compl_compl (A ∪ (B ∩ C))]
  rewrite [compl_union A (B ∩ C)]
  rewrite [compl_inter B C]
  rewrite [inter_distrib_left]
  rewrite [compl_union]
  rewrite [compl_inter]
  rewrite [compl_inter]
  rewrite [compl_compl]
  rewrite [compl_compl]
  rewrite [compl_compl]
  rfl

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x hA
  have hBC : x ∈ B ∪ C := h1 (Or.inl hA)
  rcases hBC with hB | hC
  { exact hB }
  { exact (h2 ⟨ hA, hC ⟩).left }
