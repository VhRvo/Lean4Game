import Mathlib
import Mathlib.Tactic

example (n : ℕ) : n ≤ n := by
  simp

example (n : ℕ) : n ≤ n := by
  rfl

example (n : ℤ) : 0 < n ∨ n < 0 ↔ n ≠ 0 := by
  constructor
  { intro h1 h2
    rw [h2] at h1
    simp at h1 }
  { intro h
    omega }

example (n : ℤ) : 0 < n ∨ n < 0 ↔ n ≠ 0 := by
  omega

theorem _.lt_trichotomy : ∀ a b : ℝ, a < b ∨ a = b ∨ b < a := by
  intro a b
  by_cases h_leq : a ≤ b
  { by_cases h_lt : a < b
    { left; assumption }
    { right; left; linarith } }
  { right; right; linarith }

theorem omega1 (l m n x : ℕ)
    -- (_h₁ : l ≤ m) (_h₂ : m ≤ n)
    : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  intro h hn
  omega
#print omega1

theorem omega2 (l m n x : ℕ)
    -- (_h₁ : l ≤ m) (_h₂ : m ≤ n)
    : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  omega
#print omega2

example (l m n x : ℝ)
  --  (h₁ : l ≤ m) (h₂ : m ≤ n)
   : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  intro h hn
  push_neg at hn
  rw [imp_iff_not_or] at hn
  -- obtain ⟨ h1, h2 ⟩ := h
  obtain hn | h3 := hn
  { linarith }
  { linarith }


theorem insert_Icc_eq_Icc_add_one_right.standard {a b : ℤ} (h : a ≤ b + 1)
   : insert (b + 1) (Set.Icc a b) = Set.Icc a (b + 1) := by
  ext x
  simp
  omega

theorem insert_Icc_eq_Icc_add_one_right {a b : ℤ} (h : a ≤ b + 1)
   : insert (b + 1) (Set.Icc a b) = Set.Icc a (b + 1) := by
  ext x
  simp
  constructor
  { intro h1
    obtain h2 | ⟨ h3, h4 ⟩ := h1
    { constructor
      { linarith }
      { linarith } }
    { constructor
      { linarith }
      { linarith } } }
  { intro ⟨ h1, h2 ⟩
    by_cases h3 : x = b + 1
    { left; assumption }
    { right
      constructor
      assumption
      omega } }

example (x y : ℚ)
    (h₁ : 35/11 * y ≤ 35/2 - 22/21 * x)
    (h₂ : 8/9 * y ≤ x + 17/8)
    : y ≤ 34/7 := by
  linarith

example (n x : ℕ)
    (_h : 3 ≤ n)
    : x ∈ Set.Icc 0 n \ Set.Icc 3 n → x = 0 ∨ x = 1 ∨ x = 2 := by
  simp
  omega

example (a c : ℝ)
    (h : a ≠ c)
    : ∃ b : ℝ, a < b ∧ b < c ∨ c < b ∧ b < a := by
  use (a + c) / 2
  obtain h | h | h := lt_trichotomy a c
  { left
    constructor
    repeat linarith }
  { contradiction }
  { right
    constructor
    repeat linarith }

theorem Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ)
    : a₁ ≤ b₁ → (Set.Icc a₁ b₁ ⊆ Set.Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂) := by
  intro h
  -- rw [Set.subset_def]
  unfold Set.Icc
  simp
  constructor
  { intro h1
    constructor
    { have h2 := h1 a₁
      omega }
    { have h2 := h1 b₁
      omega } }
  { intro h1
    intro x h2
    omega }

theorem Icc_subset_Icc_iff.standard (a₁ b₁ a₂ b₂ : ℕ)
    : a₁ ≤ b₁ → (Set.Icc a₁ b₁ ⊆ Set.Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂) := by
  unfold Set.Icc
  simp
  intro h₁
  constructor
  { intro h
    apply h at h₁
    -- briefly introduced in Implies, so that Luna does not depend on Spinoza
    have : a₁ ≤ a₁ := by rfl
    apply h at this
    omega }
  { omega }
