import Mathlib
import Mathlib.Tactic

example : Nonempty ℕ := by
  use 0

example (A : Type) (h : Nonempty A) : ∃ a : A, a = a := by
  obtain ⟨ e ⟩ := h
  use e

-- Robo: Specifically, someone here has provided an executable algorithm
--       for deciding whether Even 42 is true or false.
--       So if decide knows such an algorithm, it can solve the problem.
example : Even 42 := by
  decide
  -- use 21

theorem Nat.even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  obtain ⟨ e, h ⟩ := h
  use e * e * 2
  rw [h]
  ring

theorem Nat.even_square.standard (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  unfold Even at *
  choose s hs using h
  let r := 2 * s^2
  use r
  rw [hs]
  ring

example (i : ℕ) (h : Odd i): (-1 : ℤ)^i + 1 = 0 := by
  rw [Odd.neg_pow h 1]
  ring

example (i : ℕ) (h : Odd i): (-1 : ℤ)^i + 1 = 0 := by
  rw [Odd.neg_pow]
  ring
  assumption

example (i : ℕ): (-1 : ℤ)^i + (-1 : ℤ)^(i+1) = 0 := by
  -- ring
  by_cases h : Even i
  { rw [Even.neg_pow h]
    have odd : Odd (i + 1) := by
      obtain ⟨ e, h ⟩ := h
      use e
      rw [h]
      ring
    rw [Odd.neg_pow odd]
    ring }
  { apply Nat.not_even_iff_odd.mp at h
    rw [Odd.neg_pow h]
    have even : Even (i + 1) := by
      obtain ⟨ e, h ⟩ := h
      use (e + 1)
      rw [h]
      ring
    rw [Even.neg_pow even]
    ring }

#check Nat.not_even_iff_odd

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  intro x hE
  obtain ⟨ e, h ⟩ := hE
  use e
  rw [h]
  ring

-- P is, so to speak, a `mapping` that takes an element x : X and applies it to a statement.
example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  constructor
  { intro hnE
    intro x hP
    apply hnE
    use x }
  { intro hA
    intro hE
    obtain ⟨ x, hP ⟩ := hE
    apply hA
    assumption }

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  constructor
  { intro hnE
    push_neg at hnE
    assumption }
  { intro hA
    push_neg
    assumption }

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw [Nat.not_odd_iff_even]
  use n

example {People : Type} [h_nonempty : Nonempty People] (isDrinking : People → Prop)
    : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y
    := by
  by_cases hAll : ∀ y, isDrinking y
  { obtain ⟨ x ⟩ := h_nonempty
    use x
    intro
    assumption }
  { push_neg at hAll
    obtain ⟨ e, hnD ⟩ := hAll
    use e
    intro hD
    contradiction }
