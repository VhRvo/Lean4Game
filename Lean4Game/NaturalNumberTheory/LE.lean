import Mathlib.Tactic

import Lean4Game.NaturalNumberTheory.Addition

def le (a b : ℕ) := ∃ (c : ℕ), b = a + c

instance : LE Nat := ⟨ le ⟩

theorem _.le_refl (x : ℕ) : x ≤ x := by
  use 0
  rw [add_zero]

theorem _.zero_le (x : ℕ) : 0 ≤ x := by
  use x
  rw [zero_add]

theorem le_succ_self (x : ℕ) : x ≤ .succ x := by
  use 1

#check Nat.succ_eq_add_one

theorem _.le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  obtain ⟨ e1, h1 ⟩ := hxy
  obtain ⟨ e2, h2 ⟩ := hyz
  use (e1 + e2)
  -- rw [h2, h1, add_assoc]
  rw [h2, h1]
  exact add_assoc x e1 e2

theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  obtain ⟨ e, h ⟩ := hx
  exact add_right_eq_zero x e h.symm

theorem _.le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  obtain ⟨ e1, h1 ⟩ := hxy
  obtain ⟨ e2, h2 ⟩ := hyx
  -- rw [h2, add_assoc] at h1
  -- have h : e2 + e1 = 0 := add_eq_left.mp h1.symm
  -- have h' : e2 = 0 := add_right_eq_zero e2 e1 h
  -- rw [h', add_zero] at h2
  -- exact h2
  rw [h1]
  rw [h1, add_assoc] at h2
  symm at h2
  apply add_right_eq_self at h2
  apply add_right_eq_zero at h2
  rw [h2, add_zero]

theorem _.le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  cases x with
  | zero =>
    { left
      use y
      symm
      exact zero_add y }
  | succ x' =>
    { cases y with
      | zero =>
        { right
          use (x' + 1)
          symm
          exact zero_add (x' + 1) }
      | succ y' =>
        { cases le_total x' y' with
          | inl ih1 =>
            { left
              obtain ⟨ e, h ⟩ := ih1
              use e
              rw [add_right_comm, h] }
          | inr ih2 =>
            { right
              obtain ⟨ e, h⟩ := ih2
              use e
              rw [add_right_comm, h] } } }

theorem _.le_total.induction (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction x with
  | zero =>
    { left
      use y
      symm
      exact zero_add y }
  | succ x' ih =>
    { -- ih : x' ≤ y ∨ y ≤ x'
      -- ⊢ x' + 1 ≤ y ∨ y ≤ x' + 1
      induction y with
      | zero =>
        { right
          use (x' + 1)
          symm
          exact zero_add (x' + 1) }
      | succ y' ih' =>
        -- ih' : x' ≤ y' ∨ y' ≤ x' → x' + 1 ≤ y' ∨ y' ≤ x' + 1
        -- ih : x' ≤ y' + 1 ∨ y' + 1 ≤ x'
        -- ⊢ x' + 1 ≤ y' + 1 ∨ y' + 1 ≤ x' + 1
        { cases ih with
          | inl h =>
            obtain ⟨ e, h' ⟩ := h
            cases e with
            | zero =>
              { right
                rw [add_zero] at h'
                use 1
                rw [h'] }
            | succ e' =>
              { rw [add_comm e', ← add_assoc] at h'
                left
                use e' }
          | inr h =>
            obtain ⟨ e, h' ⟩ := h
            right
            use (e + 1)
            rw [h', add_assoc] } }

theorem _.le_total.stanard (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction y with
  | zero =>
  { right
    exact zero_le x }
  | succ d hd =>
  { cases hd with
    | inl h1 =>
      { left
        obtain ⟨ e, h1 ⟩ := h1
        use (e + 1)
        rw [h1, add_assoc] }
    | inr h2 =>
      { obtain ⟨ e, he ⟩ := h2
        cases e with
        | zero =>
          { left
            use 1
            rw [he, add_zero] }
        | succ e' =>
          { right
            use e'
            rw [Nat.add_succ] at he
            rw [succ_add]
            exact he } } }

theorem succ_le_succ (x y : ℕ) (hx : Nat.succ x ≤ .succ y) : x ≤ y := by
  obtain ⟨ e, h ⟩ := hx
  use e
  rw [succ_add] at h
  apply Nat.succ.inj
  exact h

theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero =>
    { left; rfl }
  | succ n' =>
    { right
      have h := le_zero n' (succ_le_succ n' 0 hx)
      rw [h] }
  -- obtain ⟨ e, h ⟩ := hx
  -- cases e with
  -- | zero =>
  --   { right
  --     rw [add_zero] at h
  --     exact h.symm }
  -- | succ e' =>
  --   { cases e' with
  --     | zero =>
  --       { symm at h
  --         -- rw [zero_add, add_left_eq_self] at h
  --         rw [zero_add, add_eq_right] at h
  --         left
  --         exact h }
  --     | succ e'' =>
  --       { repeat rw [Nat.add_succ] at h
  --         apply Nat.succ.inj at h
  --         cases Nat.succ_ne_zero (x + e'') h.symm } }

theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with
  | zero =>
    { left; rfl }
  | succ x' =>
    { right
      cases x' with
      | zero =>
        { left; rfl }
      | succ x'' =>
        { right
          have h := le_zero x'' (succ_le_succ x'' 0 (succ_le_succ (x'' + 1) 1 hx ))
          rw [h] } }
