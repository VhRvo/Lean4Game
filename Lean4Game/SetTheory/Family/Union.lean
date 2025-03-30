import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

example (A : Set U) : ∃ s, s ⊆ A := by
  exact Exists.intro A (Set.Subset.refl A)

example (A : Set U) : ∃ s, s ⊆ A := by
  exact Exists.intro ∅ (fun _ h => h.elim)

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x h
  exact Exists.intro A ⟨ h1, h ⟩

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x h
  use A

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x hUF
  obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hUF
  use W
  exact ⟨ h1 hF, hW ⟩

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  apply Iff.intro
  { intro h
    rcases h with hA | hB
    { use A
      exact ⟨ Or.inl rfl, hA ⟩ }
    { use B
      exact ⟨ Or.inr rfl, hB ⟩ } }
  { intro h
    obtain ⟨ W, ⟨ hAB, hW ⟩ ⟩ := h
    rcases hAB with hA | hB
    { rewrite [←hA]
      exact Or.inl hW }
    { rcases hB
      { exact Or.inr hW } } }

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  { intro hsU
    obtain ⟨ W, ⟨ hFG, hW ⟩ ⟩ := hsU
    rcases hFG with hF | hG
    { left; use W }
    { right; use W } }
  { intro h
    rcases h with hsU | hsU
    { obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsU
      use W
      exact ⟨ Or.inl hF, hW ⟩ }
    { obtain ⟨ W, ⟨ hG, hW ⟩ ⟩ := hsU
      use W
      exact ⟨ Or.inr hG, hW ⟩ } }

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro
  { intro h S hF x hS
    have hsU : x ∈ ⋃₀ F := by
      use S
    exact h hsU }
  { intro h x hsU
    obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsU
    exact h W hF hW }

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ { s | ∃ u ∈ F, s = A ∩ u } := by
  ext x
  apply Iff.intro
  { intro ⟨ hA, hsU ⟩
    obtain ⟨ W, ⟨ hF, hW ⟩ ⟩ := hsU
    have hAW : x ∈ A ∩ W := ⟨ hA, hW ⟩
    let G : Set (Set U) := { V | ∃ W, W ∈ F ∧ V = A ∩ W }
    have hG : (A ∩ W) ∈ G := by
      use W
    use (A ∩ W) }
  { intro hsU
    obtain ⟨ AW, ⟨ h, hAW ⟩ ⟩ := hsU
    obtain ⟨ W, ⟨ hF , heqAW ⟩ ⟩ := h
    rewrite [heqAW] at hAW
    apply And.intro
    { exact hAW.left }
    { use W
      exact ⟨ hF, hAW.right ⟩ } }
