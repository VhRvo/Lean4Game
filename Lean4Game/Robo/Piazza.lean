import Mathlib.Tactic

example : 1 ∈ ({1, 6, 4} : Set ℕ) := by
  tauto

example : 9 ∈ {n : ℕ | Odd n} := by
  use 4
  tauto

example : 9 ∈ {n : ℕ | Odd n} := by
  simp
  decide

example (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  { intro h
    obtain ⟨ hA, hB | hC ⟩ := h
    { left; constructor; repeat assumption }
    { right; constructor; repeat assumption } }
  { intro h
    obtain ⟨ hA, hB ⟩ | ⟨ hA, hC ⟩ := h
    { constructor
      { assumption }
      { left; assumption } }
    { constructor
      { assumption }
      { right; assumption } } }

example (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp
  tauto

example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = Set.univ := by
  -- rw [Set.eq_univ_iff_forall]
  simp [Set.eq_univ_iff_forall]
  intro x
  by_cases h : Even x
  { left; assumption }
  { right; rw [Nat.not_even_iff_odd] at h; assumption }

-- With generalize, you can generalize a proof goal
-- in the hope that a higher level of abstraction will allow for a simpler proof.
-- More precisely, generalize h : a = b replaces all occurrences of a in the proof goal with b
-- (and adds the assumption h : a = b).
example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  simp
  intro x
  rw [← Nat.not_even_iff_odd]
  generalize h : (Even x) = A
  tauto

example : { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  simp [Set.eq_empty_iff_forall_not_mem]

example : { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x h
  obtain ⟨ hE, hnE ⟩ := h
  simp at hnE
  rw [← Nat.not_even_iff_odd] at hnE
  contradiction

#check Set.diff

-- You:  Why is ext actually called ext?
-- Robo: Logicians call the principle that two sets are equal
--       if and only if they have the same elements extensionality.
--       And the formalists probably changed it to ext because it was too long otherwise.
example (A B : Set ℕ) : Set.univ \ (A ∩ B) = (Set.univ \ A) ∪ (Set.univ \ B) ∪ (A \ B) := by
  ext x
  simp
  constructor
  { intro h
    by_cases hA : x ∈ A
    { right; constructor; assumption; apply h; assumption }
    { left; left; assumption } }
  { intro h hA
    obtain (h1 | h2) | ⟨ h3, h4 ⟩ := h
    { contradiction }
    { assumption }
    { assumption } }

example (A B : Set ℕ) : Set.univ \ (A ∩ B) = (Set.univ \ A) ∪ (Set.univ \ B) ∪ (A \ B) := by
  ext x
  simp
  tauto

theorem _.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  { intro h
    repeat rw [h]
    simp }
  { intro h
    obtain ⟨ hAB, hBA ⟩ := h
    ext x
    constructor
    { intro h
      apply hAB
      assumption }
    { intro h
      apply hBA
      assumption } }

example {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  { intro h
    rw [h]
    tauto }
  { intro h
    ext i
    tauto }

theorem subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  constructor
  { intro h x h1
    apply h
    assumption }
  { intro h x h1
    apply h
    assumption }

example {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  constructor
  repeat tauto

example {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  tauto

example {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

example {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  intro x h
  apply h₂
  apply h₁
  assumption

example {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  rw [subset_iff] at *
  intro x h
  apply h₂
  apply h₁
  assumption

example : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  rw [subset_iff]
  intro x h
  obtain h1 | h2 | _ := h
  -- { left; tauto }
  { left; assumption }
  { right
    use 3
    simp }

example : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  intro x
  intro hx
  simp at *
  obtain h | h := hx
  { tauto }
  { right
    rw [h]
    decide }

example (A : Finset ℕ) (a : ℕ) : Finset.erase A a = A \ {a} := by
  ext x
  simp
  tauto

example (A : Finset ℕ) (a : ℕ) : insert a A = A ∪ {a} := by
  ext x
  simp
  tauto

theorem insert_erase
    {A : Type} [h : DecidableEq A]
    {s : Finset A} {a : A} (h : a ∈ s)
    : insert a (Finset.erase s a) = s := by
  ext x
  simp
  constructor
  { intro h1
    obtain h1 | h1 := h1
    { rw [h1]; assumption }
    { obtain ⟨ _, _ ⟩ := h1
      assumption } }
  { intro h1
    by_cases h2 : x = a
    { left; assumption }
    { right
      constructor
      repeat assumption } }
