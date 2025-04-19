example (P Q R : Prop) (hP : P) (_ : Q) (_ : R) : P := by
  exact hP

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  { exact hP }
  { exact hQ }

example (hP : P) : P ∨ Q := by
  left
  exact hP

example {P Q : Prop} (hP : P) (ptoq: P → Q) : Q := by
  exact ptoq hP

example {P :Prop} : P → P := by
  intro h
  exact h

example {P Q R : Prop} (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP => exact hPR hP
  | inr hQ => exact hQR hQ

example (PsameQ : P ↔ Q) (hP : P) : Q := by
  rw [←PsameQ]
  exact hP

example (PsameQ : P ↔ Q) (hP : P) : Q := by
  rw [PsameQ] at hP
  exact hP

example (PsameQ : P ↔ Q) (hP : P) : Q := by
  exact PsameQ.mp hP

example {P: Prop} {hP : P} {hnP : ¬P} : False := by
  exact hnP hP

example {P: Prop} {hP : P} {hnP : ¬P} : False := by
  unfold Not at hnP
  exact hnP hP

example {Q : Prop} (hF : False) : Q := by
  exact hF.elim

example {Q : Prop} (hF : False) : Q := by
  contradiction

theorem not_left_right {P Q : Prop} (hOr : P ∨ Q) (hnP : ¬P) : Q := by
  cases hOr with
  | inl hp => exact (hnP hp).elim
  | inr hq => exact hq

example {P Q : Prop} (hOr : P ∨ Q) (hnP : ¬P) : Q := by
  simp [hnP] at hOr
  exact hOr

theorem notright_left {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) (hPF : P ∨ False → P) : P := by
  have hQisFalse : Q = False := eq_false notright
  simp [hQisFalse] at Or
  exact Or
