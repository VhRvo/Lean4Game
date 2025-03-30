import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.SetNotation

-- Complement of a family union
example (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ { s | sᶜ ∈ F } := by
  ext x
  apply Iff.intro
  { intro hnsU S hcF
    rewrite [Set.mem_setOf] at hcF
    by_contra hnS
    have h : x ∈ ⋃₀ F := by
      use Sᶜ
      exact ⟨ hcF, hnS ⟩
    exact hnsU h }
  { intro h h1
    obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := h1
    rewrite [←compl_compl W] at hF
    exact h Wᶜ hF hW }

-- Complement of a family intersection
theorem compl_of_sInter (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ { s | sᶜ ∈ F } := by
  ext x
  apply Iff.intro
  { intro hnsI
    by_contra hnsU
    apply hnsI
    intro W hF
    by_contra hnW
    apply hnsU
    use Wᶜ
    apply And.intro
    { rewrite [Set.mem_setOf]
      rewrite [compl_compl]
      exact hF }
    { exact hnW }
     }
  { intro h hsI
    obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := h
    rewrite [Set.mem_setOf] at hF
    have hnW : x ∈ Wᶜ := hsI Wᶜ hF
    exact hnW hW }

-- Two families with an element in common
example (F G : Set (Set U))
  (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t)
  (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s)
  : ∃ u, u ∈ F ∩ G := by
  obtain ⟨ w, ⟨ hF, h ⟩ ⟩ := h2
  use w
  apply And.intro
  { exact hF }
  { obtain ⟨ t, ⟨ hG, hwt ⟩ ⟩ := h1 w hF
    have htw := h t hG
    rewrite [Set.Subset.antisymm htw hwt] at hG
    exact hG }

example (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H)
  : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x ⟨ hsU, hsI ⟩
  obtain ⟨ W1, ⟨ hF, hW1 ⟩ ⟩ := hsU
  obtain ⟨ W2, ⟨ hG, hW1W2 ⟩ ⟩ := h1 W1 hF
  have hW2 := hsI W2 hG
  use (W1 ∩ W2)
  exact ⟨ hW1W2, ⟨ hW1, hW2 ⟩ ⟩

-- A union intersected with the complement of another is a subset
example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x ⟨ hsU, hnsU ⟩
  obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsU
  use W
  apply And.intro
  { apply And.intro
    { exact hF }
    { intro hG
      apply hnsU
      use W } }
  { exact hW }

-- A subset of a union intersected with the complement of another
example (F G : Set (Set U))
  (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ)
  : (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x ⟨ hsUF, hsUG ⟩
  obtain ⟨ W1, ⟨ hF, hW1 ⟩ ⟩ := hsUF
  obtain ⟨ W2, ⟨ hG, hW2 ⟩ ⟩ := hsUG
  use W1
  apply And.intro
  { apply And.intro
    { exact hF }
    { by_contra h
      obtain ⟨ _, hnsG ⟩ := h1 (by
        use W1
        exact ⟨ ⟨ hF, h ⟩, hW1 ⟩)
      apply hnsG
      use W2 } }
  { exact hW1 }

-- A union intersected with the complement of an intersection
example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ { s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ v ᶜ }
  := by
  intro x ⟨ hsUF, hnsI ⟩
  obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsUF
  rewrite [compl_of_sInter G] at hnsI
  have ⟨ V, ⟨ hG, hV ⟩ ⟩ := hnsI
  use (W ∩ V)
  apply And.intro
  { use W
    apply And.intro
    { exact hF }
    { use Vᶜ
      apply And.intro
      { exact hG }
      { rewrite [compl_compl V]
        rfl } } }
  { exact ⟨ hW, hV ⟩ }

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ { s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ v ᶜ }
  := by
  intro x ⟨ hsUF, hnsI ⟩
  obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsUF
  by_contra h
  apply hnsI
  intro V hG
  by_contra hnV
  apply h
  use (W ∩ Vᶜ)
  apply And.intro
  { use W
    apply And.intro
    { exact hF }
    { use V } }
  { exact ⟨ hW, hnV ⟩ }

example (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  have h2 := h1 { s | ∃ x , s = { x } ∧ x ∈ A} (by
    apply Set.Subset.antisymm
    { intro x h
      obtain ⟨ W, ⟨ h₀, hW ⟩ ⟩ := h
      obtain ⟨ x1, ⟨ hdW, hA ⟩ ⟩ := h₀
      rewrite [hdW] at hW
      rewrite [Set.mem_singleton_iff.mp hW]
      exact hA }
    { intro x h
      use {x}
      apply And.intro
      { use x }
      { rfl } } )
  obtain ⟨ x, ⟨ h, _ ⟩ ⟩ := h2
  use x
