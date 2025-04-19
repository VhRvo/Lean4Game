import Init.Data.Nat.Lemmas

example : 2 = 2 := by
  rfl

example (h : x = 2) : x = 2 := by
  exact h

example (h : x = 2) : x = 2 := by
  assumption

-- rw takes a term of type A=B and replaces all the As in the goal with Bs.
example (h : x = 3) (g : y = 6) (_ : z = 10) : x + x = y := by
  rw [h, g]

example (h : 4 * y = 16) : y = 4 := by
  exact Nat.mul_left_cancel (by simp) h

example (h : 4 * y = 16) : y = 4 := by
  have h1 : 4 * y = 4 * 4 := h
  have h2 := Nat.mul_left_cancel (by simp) h1
  exact h2
