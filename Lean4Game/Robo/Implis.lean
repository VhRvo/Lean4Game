import Mathlib.Tactic

-- You: We assume that B is true and want to
--      show that then A implies A and B.
example (A B : Prop) (hB : B) : A → (A ∧ B) := by
  intro hA
  constructor
  repeat assumption

example (A B : Prop) (hA : A) (h : A → B) : B := by
  revert hA
  assumption

example (A B : Prop) (h : A) (hAB : A → B) : B := by
  apply hAB at h
  assumption

example (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  intro h
  apply f at h
  apply g at h
  assumption

example (A B C D E F G H I : Prop)
   (f : A → B) (g : C → B) (h : A → D) (i : B → E)
   (j : C → F) (k : E → D) (l : E → F) (m : G → D)
   (n : H → E) (p : F → I) (q : H → G) (r : H → I)
   : A → I := by
  intro h
  apply p
  apply l
  apply i
  apply f
  -- apply f at h
  -- apply i at h
  -- apply l at h
  -- apply p at h
  assumption

-- You: So h.mp is A → B? Why mp?
-- Robo: mp stands for modus ponens.
--       Modus ponens is a reasoning figure already common in ancient logic,
--       which in many logical systems...  Oh no, you didn't want to hear that.
--       The "r" in mpr stands for "reverse," because it's the reverse direction.
example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  repeat assumption

example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  symm
  assumption

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw [h₁]
  rw [← h₂]
  assumption

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  trans
  symm; assumption
  trans
  assumption
  symm; assumption

example (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  intro hA
  apply g
  apply h.mp
  assumption

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro h
  obtain ⟨ _, _ ⟩ := h
  assumption

example (A : Prop) : ¬A ∨ A := by
  by_cases h : A
  { right; assumption }
  { left; assumption }

example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  repeat rw [not_not]

theorem _.imp_iff_not_or {A B : Prop} : (A → B) ↔ ¬ A ∨ B := by
  constructor
  { intro h
    by_cases hA : A
    { right; apply h; assumption }
    { left; assumption } }
  { intro h hA
    obtain hnA | hB := h
    { contradiction }
    { assumption } }
