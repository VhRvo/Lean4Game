import Mathlib.Tactic

theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  rw [pow_zero]

theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (.succ m) = 0 := by
  rw [pow_succ, mul_zero]

theorem _.pow_one (a : ℕ) : a ^ 1 = a := by
  rw [pow_succ, pow_zero, one_mul]

theorem _.one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with
  | zero => rw [pow_zero]
  | succ n' ih => rw [pow_succ, mul_one, ih]

theorem _.pow_two (a : ℕ) : a ^ 2 = a * a := by
  repeat rw [pow_succ]
  rw [pow_zero, one_mul]

theorem _.pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [add_zero, pow_zero, mul_one]
  | succ n' ih =>
    rw [Nat.add_succ, pow_succ, pow_succ, ih, mul_assoc]

theorem _.mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rw [Nat.pow_zero]
  | succ n' ih =>
    repeat rw [pow_succ]
    rw [ih, mul_assoc, ← mul_assoc (b ^ n'), mul_comm (b ^ n')]
    rw [mul_assoc, ← mul_assoc]

theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [pow_zero, mul_zero, pow_zero]
  | succ n' ih =>
    rw [pow_succ, Nat.mul_succ, pow_add, ih]

theorem _.add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  repeat rw [pow_two]
  rw [add_mul]
  repeat rw [mul_add]
  rw [mul_comm b a, add_assoc]
  nth_rewrite 2 [← add_assoc]
  rw [← two_mul, ← mul_assoc, add_comm (2 * a * b), ← add_assoc]

theorem add_cube (a b : ℕ) : (a + b) ^ 3 = a ^ 3 + b ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 := by
  sorry

example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry
