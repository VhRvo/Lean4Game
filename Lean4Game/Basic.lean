def hello := "world"

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (sorry)
    (by
     intro (hp : P t) (x : α) (heq : x = t)
     show P x
     rw [heq]
     exact hp)
