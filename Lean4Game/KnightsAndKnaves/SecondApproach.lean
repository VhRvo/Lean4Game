example
    {A B C : Prop}
    {stA : A ↔ (B ∧ C)} {_stAn : ¬A ↔ ¬(B ∧ C)}
    {stB : B ↔ (C ∧ ¬A)} {_stBn : ¬B ↔ ¬C ∨ A} : ¬A ∧ ¬B ∧ ¬C
    := by
  constructor
  { intro hA
    have hB := (stA.mp hA).left
    have hnA := (stB.mp hB).right
    exact hnA hA }
  { constructor
    { intro hB
      have ⟨ hC, hnA ⟩ := stB.mp hB
      have hA := stA.mpr ⟨ hB, hC ⟩
      exact hnA hA }
    { intro hC
      have hB := stB.mpr ⟨ hC, λ hA ↦ (stB.mp (stA.mp hA).left).right hA ⟩
      have hA := stA.mpr ⟨ hB, hC ⟩
      have hnA := (stB.mp hB).right
      exact hnA hA } }
