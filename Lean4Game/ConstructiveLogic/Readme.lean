def readme := id <| "too easy"

example {A B : Prop} : True := by
  let f : A ∧ B → B ∧ A := λ ⟨ h1, h2 ⟩ ↦ ⟨ h2, h1 ⟩
  simp

example (P Q R S : Prop) (h1 : R ↔ S) (h2 : ¬((P → Q ∨ ¬S) ∧ (S ∨ P → ¬Q) → (S → Q)) ↔ P ∧ Q ∧ ¬S) : ¬((P → Q ∨ ¬R) ∧ (R ∨ P → ¬Q) → (R → Q)) ↔ P ∧ Q ∧ ¬R := by
  constructor
  { intro h
    apply ((λ ⟨ hP, ⟨ hQ, hnS ⟩ ⟩ ↦ ⟨ hP, hQ, λ hR ↦ hnS (h1.mp hR) ⟩) : P ∧ Q ∧ ¬S → _ )
    apply h2.mp
    intro h₁
    apply h
    intro h₂ hR
    apply h₁
    constructor
    { intro hP
      apply ((λ h₄ ↦ Or.elim h₄ (λ hQ => Or.inl hQ) (λ hnR => Or.inr (λ hS ↦ hnR hR))) : (Q ∨ ¬ R) → (Q ∨ ¬ S))
      apply h₂.left
      assumption }
    { intro hSP hQ
      cases hSP with
      | inl hS =>
        apply h₂.right
        left
        assumption
        assumption
      | inr hP =>
        apply h₂.right
        left
        assumption
        assumption }
    { apply h1.mp
      assumption } }
  { intro ⟨ hP, ⟨ hQ, hnR ⟩ ⟩ h
    apply h2.mpr
    { constructor
      { assumption }
      { constructor
        { assumption }
        { intro hS
          apply hnR
          apply h1.mpr
          assumption } } }
    { intro hAnd hS
      apply h
      { constructor
        { intro _
          left
          assumption }
        { intro hRP
          apply hAnd.right
          left
          assumption } }
      { apply h1.mpr; assumption } } }

example (P Q R : Prop): (P ∧ Q ↔ R ∧ Q) ↔ Q → (P ↔ R) := by
  constructor
  { intro h hQ
    constructor
    { intro hP
      exact (h.mp ⟨ hP, hQ ⟩ ).left }
    { intro hR
      exact (h.mpr ⟨ hR, hQ ⟩ ).left } }
  { intro h
    constructor
    { intro ⟨ hP, hQ ⟩
      rw [←h hQ]
      constructor
      repeat assumption }
    { intro ⟨ hR, hQ ⟩
      rw [h hQ]
      constructor
      repeat assumption } }
