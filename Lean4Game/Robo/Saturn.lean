import Mathlib
import Mathlib.Tactic

example (a b c d : ℝ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw [h₁, ← h₂, ← h₃]

example (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  -- rw [add_pow_two]
  ring

namespace MvPolynomial
example (P : MvPolynomial (Fin 2) ℚ) : (X 0) * P = P * (X 0) := by
  rw [mul_comm]

-- You:  But wait a minute, this time the coefficients were in ℕ!
--       That's not a ring at all, and polynomials
--       with coefficients in ℕ don't form a ring either.
-- Robo: Maybe. But ring even works for so-called semirings.
example (a b c : MvPolynomial (Fin 4) ℕ ) : a * b * c = a * (b * c) := by
  rw [mul_assoc]

example (A B : MvPolynomial (Fin 4) ℝ)
    (hA : A = (X 0)*(X 3) - (X 1)*(X 2))
    (hB : B = (X 0)*(X 2) + (X 1)*(X 3))
    : ((X 0)^2 + (X 1)^2) * ((X 2)^2 + (X 3)^2) = A^2 + B^2 := by
  rw [hA, hB]
  ring

end MvPolynomial
