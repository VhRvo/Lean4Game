import Mathlib.Tactic

theorem _.zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rw [add_zero]
  | succ n' ih => rw [Nat.add_succ, ih]

theorem succ_add (a b : ℕ) : .succ a + b = .succ (a + b) := by
  induction b with
  | zero => rw [add_zero, add_zero]
  | succ n' ih => rw [Nat.add_succ, ih, Nat.add_succ]

theorem _.add_comm (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ n' ih => rw [Nat.add_succ, succ_add, ih]

theorem _.add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rw [add_zero, add_zero]
  | succ n' ih => rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

theorem _.add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, add_assoc]

theorem _.add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with
  | zero =>
    { repeat rw [add_zero]
      exact id }
  | succ n' ih =>
    { repeat rw [Nat.add_succ]
      intro h
      apply Nat.succ.inj at h
      exact ih h  }

theorem _.add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  repeat rw [add_comm n]
  exact add_right_cancel a b n

theorem _.add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  nth_rewrite 2 [← Nat.zero_add y]
  exact add_right_cancel x 0 y

theorem _.add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw [add_comm]
  exact add_left_eq_self y x
  -- nth_rewrite 2 [← Nat.add_zero x]
  -- exact add_left_cancel y 0 x

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with
  | zero =>
    -- exact _.add_left_eq_self a 0
    exact add_eq_right.mp
  | succ b' =>
    { rw [Nat.add_succ]
      intro h
      cases Nat.succ_ne_zero (a + b') h }

#check add_eq_right

theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw [add_comm]
  exact add_right_eq_zero b a
