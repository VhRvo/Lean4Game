import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x h
  rewrite [Set.mem_sInter] at h
  exact h A h1

-- Intersecting larger collection of sets leads to a smaller result.
example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h A hF
  have hG : A ∈ G := h1 hF
  exact h A hG

-- If A and B are sets, then A ∩ B is equal to the intersection of
-- the family of sets that contains just A and B and nothing else.
example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro
  { intro h F hAB
    rcases hAB with hFA | hFB
    { rewrite [hFA]
      exact h.left }
    { rewrite [hFB]
      exact h.right } }
  { intro hAB
    have hA : x ∈ A := hAB A (Or.inl rfl)
    have hB : x ∈ B := hAB B (Or.inr rfl)
    exact ⟨ hA, hB ⟩ }

-- x ∈ ⋂₀ (F ∪ G)
-- ↔ ∀ S. S ∈ (F ∪ G) → x ∈ S
-- ↔ ∀ S. (S ∈ F) ∪ (S ∈ G) → x ∈ S
-- ↔ ∀ S. (S ∈ F → x ∈ S) ∧ (S ∈ G → x ∈ S)
-- ↔ (∀ S. S ∈ F → x ∈ S) ∧ (∀ S. S ∈ G → x ∈ S)
-- ↔ x ∈ ⋂₀ F ∧ x ∈ ⋂₀ G
example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  apply Iff.intro
  { intro hsI
    apply And.intro
    { intro S hF
      have hS : x ∈ S := hsI S (Or.inl hF)
      exact hS }
    { intro S hG
      have hS : x ∈ S := hsI S (Or.inr hG)
      exact hS } }
  { intro h S hFG
    rcases hFG with hF | hG
    { exact h.left S hF }
    { exact h.right S hG } }

example (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  apply Iff.intro
  { intro hsI S hF x hA
    have hS := hsI hA S hF
    exact hS }
  { intro h x hA S hF
    have hS := h S hF hA
    exact hS }

example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x h
  by_cases hA : x ∈ A
  { exact Or.inl hA }
  { apply Or.inr
    intro S hF
    have hAS : x ∈ A ∪ S := h (A ∪ S) (h1 S hF)
    rcases hAS with hA' | hS
    { exact (hA hA').elim }
    { exact hS } }
