import Mathlib.Tactic

example (A B C : Prop) : ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

example : 42 = 42 := by
  rfl

example (n : ℕ) (_h₁ : 10 > n) (h₂ : 1 < n) (_h₃ : n ≠ 5) : 1 < n := by
  assumption

example (A : Prop) (hA : A) : A := by
  assumption

-- Robo: `decide` only works in special situations
--       where there's a simple algorithm that decides
--       whether the statement is true.
example : True := by
  decide

example : ¬False := by
  decide

-- Robo: As we all know, anything can be proven from a false assumption.
-- You:  Was that a proof by contradiction?
-- Robo: No, a proof by contradiction looks different.
--       The argument here was:
--       we have a contradiction in our assumptions,
--       so any statement follows.
example (A : Prop) (h : False) : A := by
  contradiction

-- You: But somehow it still seems a little suspect to me.
--      Now I've proven that any natural number is equal to 37?
-- Robo: No, not at all.
--       Only any number that is not equal to itself is equal to 37.
--       And equal to 38, and equal to 39, ...
example (n : ℕ) (h : n ≠ n) : n = 37 := by
  contradiction

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  contradiction

example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  constructor
  repeat assumption

example (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  -- obtain ⟨ _, ⟨ h, _ ⟩ ⟩ := h
  obtain ⟨ _, _, _ ⟩ := h
  assumption

-- You:  Do I have to deconstruct the proof again?
-- Robo: No, much simpler.
--       If you're supposed to prove an OR statement,
--       you simply have to decide
--       whether you want to prove the left or right side.
example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  left
  assumption

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  obtain h | h := h
  { obtain ⟨ _, _⟩ := h
    assumption }
  { assumption }

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  obtain h | h := h
  { constructor
    left; assumption
    left; assumption }
  { obtain ⟨ _, _ ⟩ := h
    constructor
    repeat { right; assumption } }
