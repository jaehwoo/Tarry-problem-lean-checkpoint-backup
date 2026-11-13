import PaperILean.PolynomialFiberDegree
import PaperILean.PublishedHardtTriviality

/-! Exact specialization of a finite polynomial-sign description to an actual
fiber. The number of polynomials and the degree bound do not increase.
Pre-strategy map tests, including cancellation, degree drops and empty/full
fibers, were executed in checkpoint_103_041_fiber_sign_obstructions.log. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def specializePolynomialFamily {ι κ : Type*} (p : ι → ℝ)
    (A : Finset (MvPolynomial (ι ⊕ κ) ℝ)) : Finset (MvPolynomial κ ℝ) :=
  A.image (specializePolynomialFiber p)

theorem specializePolynomialFamily_card_le {ι κ : Type*} (p : ι → ℝ)
    (A : Finset (MvPolynomial (ι ⊕ κ) ℝ)) :
    (specializePolynomialFamily p A).card ≤ A.card := Finset.card_image_le

theorem specializePolynomialFamily_totalDegree_le {ι κ : Type*} (p : ι → ℝ)
    (A : Finset (MvPolynomial (ι ⊕ κ) ℝ)) (D : ℕ)
    (hA : ∀ q ∈ A, q.totalDegree ≤ D) :
    ∀ q ∈ specializePolynomialFamily p A, q.totalDegree ≤ D := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  exact (specializePolynomialFiber_totalDegree_le p r).trans (hA r hr)

/-- The original sign predicate is evaluated with one common fixed base p. -/
theorem polynomialSignDetermined_projectionFiber {ι κ : Type*}
    (p : ι → ℝ) (A : Finset (MvPolynomial (ι ⊕ κ) ℝ))
    (S : Set ((ι ⊕ κ) → ℝ)) (hS : PolynomialSignDetermined A S) :
    PolynomialSignDetermined (specializePolynomialFamily p A) (projectionFiber S p) := by
  intro x y hxy
  apply hS (Sum.elim p x) (Sum.elim p y)
  intro q hq
  have h := hxy (specializePolynomialFiber p q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  simpa only [specializePolynomialFiber_eval] using h

/-- Exact bounded sign format for every fiber, without any nonvanishing
coefficient, nonempty fiber, compactness, or finite base-coordinate premise. -/
theorem projectionFiber_has_bounded_sign_format {ι κ : Type*}
    (p : ι → ℝ) (A : Finset (MvPolynomial (ι ⊕ κ) ℝ))
    (S : Set ((ι ⊕ κ) → ℝ)) (s D : ℕ)
    (hcard : A.card ≤ s) (hdegree : ∀ q ∈ A, q.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) :
    ∃ B : Finset (MvPolynomial κ ℝ), B.card ≤ s ∧
      (∀ q ∈ B, q.totalDegree ≤ D) ∧ PolynomialSignDetermined B (projectionFiber S p) :=
  ⟨specializePolynomialFamily p A,
    (specializePolynomialFamily_card_le p A).trans hcard,
    specializePolynomialFamily_totalDegree_le p A D hdegree,
    polynomialSignDetermined_projectionFiber p A S hS⟩

end PaperI
