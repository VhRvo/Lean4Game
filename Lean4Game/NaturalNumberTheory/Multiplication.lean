import Mathlib.Tactic

import Lean4Game.NaturalNumberTheory.LE

theorem _.mul_one (m : ℕ) : m * 1 = m := by
  rw [Nat.mul_succ]
  rw [mul_zero]
  rw [zero_add]

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [mul_zero]
  | succ m' ih =>
    rw [Nat.mul_succ, add_zero, ih]

theorem succ_mul (a b : ℕ) : .succ a * b = a * b + b := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero, add_zero]
  | succ n' ih =>
    rw [ Nat.mul_succ, Nat.mul_succ
       , ih, Nat.add_succ, Nat.add_succ
       , add_right_comm
       ]

theorem _.mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with
  | zero => rw [mul_zero, zero_mul]
  | succ n' ih =>
    rw [Nat.mul_succ, succ_mul, ih]
#check Nat.mul_comm

theorem _.one_mul (m : ℕ): 1 * m = m := by
  -- rw [_.mul_comm]
  -- apply _.mul_one
  rw [mul_comm, mul_one]
#check Nat.one_mul

theorem _.two_mul (m : ℕ): 2 * m = m + m := by
  rw [succ_mul, one_mul]
#check two_mul

theorem _.mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [add_zero, mul_zero, add_zero]
  | succ n' ih =>
    rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, add_assoc]

theorem _.add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add]
  repeat rw [mul_comm c]

theorem _.mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    repeat rw [mul_zero]
  | succ n' ih =>
    rw [Nat.mul_succ, Nat.mul_succ, mul_add, ih]

theorem _.mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  obtain ⟨ e, h1 ⟩ := h
  use (e * t)
  rw [h1, add_mul]

theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  contrapose! h
  rw [h, mul_zero]

theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = .succ n := by
  cases a with
  | zero =>
    tauto
  | succ a' =>
    use a'

theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  cases a with
  | zero =>
    tauto
  | succ a' =>
    use a'
    rw [add_comm]

theorem one_le_of_ne_zero.standard (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  apply eq_succ_of_ne_zero at ha
  obtain ⟨ n, hn ⟩ := ha
  use n
  rw [hn, add_comm]

theorem _.le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply eq_succ_of_ne_zero at h
  obtain ⟨ b', h ⟩ := h
  use a * b'
  rw [h, Nat.mul_succ, add_comm]

theorem _.le_mul_right.standard (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply one_le_of_ne_zero at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul, mul_comm] at h
  exact h

theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h2 : x * y ≠ 0 := by
    rw [h]
    exact Nat.succ_ne_zero 0
  apply _.le_mul_right x y at h2
  rw [h] at h2
  cases le_one x h2 with
  | inl h1 =>
    { rw [h1] at h ⊢
      rw [zero_mul] at h
      exact h }
  | inr h2 =>
    { exact h2 }

theorem _.mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  obtain ⟨ a', ha ⟩ := eq_succ_of_ne_zero a ha
  obtain ⟨ b', hb ⟩ := eq_succ_of_ne_zero b hb
  intro h
  rw [ha, hb, Nat.mul_succ, Nat.add_succ] at h
  tauto

theorem _.mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | zero =>
    left; rfl
  | succ a' =>
    cases b with
    | zero =>
      right; rfl
    | succ b' =>
      rw [Nat.mul_succ, Nat.add_succ] at h
      tauto

theorem _.mul_eq_zero.standard (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have h2 := mul_ne_zero a b
  tauto

theorem _.mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b generalizing c with
  | zero =>
    { rw [mul_zero] at h
      symm at h
      cases mul_eq_zero a c h with
      | inl h' =>
        { tauto }
      | inr h' =>
        -- { symm; exact h' }
        { rw [h'] } }
  | succ b' ih =>
    { cases c with
      | zero =>
        -- { rw [mul_zero] at h
        --   have hn := mul_ne_zero a (b' + 1) ha (Nat.succ_ne_zero b')
        --   tauto }
        { rw [Nat.mul_succ, mul_zero] at h
          apply add_left_eq_zero at h
          tauto }
      | succ c' =>
        { repeat rw [Nat.mul_succ] at h
          apply add_right_cancel at h
          apply ih c' at h
          rw [h] } }

theorem _.mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  nth_rewrite 2 [← mul_one a] at h
  exact mul_left_cancel a b 1 ha h
  -- cases b with
  -- | zero =>
  --   { rw [mul_zero] at h
  --     tauto }
  -- | succ b' =>
  --   { rw [Nat.mul_succ] at h
  --     apply add_left_eq_self at h
  --     apply mul_eq_zero at h
  --     cases h with
  --     | inl h' =>
  --       tauto
  --     | inr h' =>
  --       rw [h'] }
