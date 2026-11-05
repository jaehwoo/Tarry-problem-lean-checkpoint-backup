import PaperILean.PolynomialSignDescription
import Mathlib.Algebra.MvPolynomial.Monad

/-! Finite polynomial-sign descriptions pull back along actual polynomial maps.
This is direct polynomial substitution, not quantifier elimination. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable

theorem polynomialSignDetermined_polynomial_preimage {α β : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined A S) (q : α → MvPolynomial β ℝ) :
    PolynomialSignDetermined (A.image (MvPolynomial.bind₁ q))
      {x : β → ℝ | (fun i => MvPolynomial.eval x (q i)) ∈ S} := by
  classical
  intro x y hxy
  apply hS
  intro p hp
  have h := hxy (MvPolynomial.bind₁ q p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  simpa only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁] using h

theorem hasPolynomialSignDescription_polynomial_preimage {α β : Type*}
    {S : Set (α → ℝ)} (hS : HasPolynomialSignDescription S)
    (q : α → MvPolynomial β ℝ) :
    HasPolynomialSignDescription
      {x : β → ℝ | (fun i => MvPolynomial.eval x (q i)) ∈ S} := by
  obtain ⟨A,hA⟩ := hS
  exact ⟨_,polynomialSignDetermined_polynomial_preimage A S hA q⟩

end PaperI
