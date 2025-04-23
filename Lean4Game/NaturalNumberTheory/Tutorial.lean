import Init.Prelude
import Mathlib.Tactic

example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

example : 2 = .succ (.succ 0) := by
  rfl

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [Nat.add_zero]
  -- rw [Nat.add_zero]
  -- rw [Nat.add_zero]

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [Nat.add_zero c]
  rw [Nat.add_zero b]

theorem succ_eq_add_one (n : ℕ) : Nat.succ n = n + 1 := by
  rw [Nat.add_succ]

example : (2 : ℕ) + 2 = 4 := by
  rfl
