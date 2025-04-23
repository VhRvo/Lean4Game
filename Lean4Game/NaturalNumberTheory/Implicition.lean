import Mathlib.Tactic

example (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  simp at h
  exact h

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  apply Nat.succ.inj at h
  exact h

#check Nat.succ_inj

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  apply Nat.succ.inj
  exact h

example (x : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  apply Nat.succ.inj
  exact h

theorem _.zero_ne_one : (0 : ℕ) ≠ 1 := by
  intro h
  apply Nat.succ_ne_zero 0
  exact h.symm

theorem _.one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  apply Nat.zero_ne_one

example : Nat.succ (.succ 0) + .succ (.succ 0) ≠ .succ (.succ (.succ (.succ (.succ 0)))) := by
  intro h
  repeat rw [Nat.add_succ] at h
  repeat rw [Nat.add_zero] at h
  repeat apply Nat.succ.inj at h
  exact Nat.zero_ne_one h
