-- import Mathlib
import Mathlib.Tactic
import Lean4Game.Robo.Quantus

example (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  obtain ⟨ hA, hB ⟩ := k
  apply h
  repeat assumption

example (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  apply h
  repeat assumption

example (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  suffices g : ¬ B
  { contradiction }
  { apply h
    assumption }

example (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  by_contra h -- intro h
  apply g at h
  contradiction

theorem _.not_imp_not (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  constructor
  { intro h hnB hA
    apply hnB
    apply h hA }
  { intro h hA
    by_contra hnB
    apply h hnB hA }

example (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  constructor
  { intro h b
    by_contra a
    suffices b : B
    { contradiction }
    { apply h
      assumption } }
  { intro h a
    by_contra b
    suffices g : ¬ A
    { contradiction }
    { apply h
      assumption } }

#check Nat.even_square

example (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  revert h
  contrapose
  repeat rw [Nat.not_odd_iff_even]
  apply Nat.even_square

example (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  by_contra g
  rw [Nat.not_odd_iff_even] at g
  have h1 := Nat.even_square n g
  rw [← Nat.not_even_iff_odd] at h
  contradiction

example (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  by_contra g
  suffices d : ¬ (Odd (n ^ 2))
  { contradiction }
  { rw [Nat.not_odd_iff_even] at *
    apply Nat.even_square
    assumption }
