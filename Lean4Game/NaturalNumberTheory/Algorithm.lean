import Mathlib.Tactic

theorem _.add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a, add_assoc]

example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  -- rw [add_assoc, add_comm b, add_assoc, ← add_assoc, ← add_assoc]
  -- rw [ add_assoc a c, add_assoc, add_left_comm b c d
  --    , add_comm b d, ← add_assoc c, ← add_assoc]
  repeat rw [add_assoc]
  rw [add_left_comm b c, add_comm b d]

example (a b c d e f g h : ℕ)
    : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
  := by
  simp only [add_assoc, add_left_comm, add_comm]
  -- simp only [add_assoc, add_right_comm, add_comm] -- Why this simp tactic failed?

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

example (a b c d e f g h : ℕ)
    : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
  := by
  simp_add

def pred : ℕ → ℕ
  | .zero => 42
  | .succ n' => n'

theorem pred_succ (n : ℕ) : pred (.succ n) = n := by
  rfl

theorem succ_inj {a b : ℕ} (h : Nat.succ a = .succ b) : a = b := by
  rw [← pred_succ a, ← pred_succ b, h]

def is_zero : ℕ → Prop
  | .zero => True
  | .succ _ => False

theorem is_zero_zero : is_zero .zero = True := by
  rfl

theorem is_zero_succ (n : ℕ) : is_zero (.succ n) = False := by
  rfl

theorem succ_ne_zero (a : ℕ) : .succ a ≠ 0 := by
  intro h
  rw [← is_zero_succ a, h, is_zero_zero]
  trivial

theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : Nat.succ m ≠ .succ n := by
  contrapose! h
  rw [succ_inj h]

example : (20 : ℕ) + 20 = 40 := by
  decide

#check DecidableEq

instance instDecidableEq : DecidableEq ℕ
| .zero, .zero => isTrue <| by
  show 0 = 0
  rfl
| .zero, .succ n => isFalse <| by
  exact (succ_ne_zero n).symm
| .succ m, .zero => isFalse <| by
  exact succ_ne_zero m
| .succ m, .succ n => by
  cases instDecidableEq m n with
  | isTrue h =>
    apply isTrue
    rw [h]
  | isFalse h =>
    apply isFalse
    exact succ_ne_succ m n h

example : (2 : ℕ) + 2 ≠ 5 := by
  decide
