import PaperILean.AugmentedOrbit

/-! The translation stop forces a nonconstant full directional derivative
when the same nonzero direction is killed by the physical matrix. Constants
are discarded only after the full derivative has been identified. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem directionalCoefficientMap_eq_zero_of_constant {k : ℕ}
    (F : CoefficientSpace k) (h : PhysicalSpace) (c : ℝ)
    (hc : directionalPolynomialPartial h (coefficientPolynomial F) = MvPolynomial.C c) :
    directionalCoefficientMap k h F = 0 := by
  apply (coefficientPolynomialEquiv k).injective
  apply Subtype.ext
  change coefficientPolynomial (directionalCoefficientMap k h F) = _
  rw [polynomial_directionalCoefficientMap, hc]
  simp [coefficientPolynomial]

theorem stopped_directionalPolynomialPartial_nonconstant {k : ℕ} {P : ℝ}
    (hP : 0 < P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (h : PhysicalSpace) (hh : h ≠ 0) (hM : S.2.2 *ᵥ h = 0) (c : ℝ) :
    directionalPolynomialPartial h (coefficientPolynomial S.1) ≠ MvPolynomial.C c := by
  intro hc
  have hz : augmentedOrbitDifferential k S (upperAffineTranslationCoordinates h) = 0 := by
    rw [augmentedOrbit_translation, directionalCoefficientMap_eq_zero_of_constant S.1 h c hc,
      hM]
    rfl
  exact hh (augmentedOrbit_translation_eq_zero hP S hstop h hz)

theorem directionalPolynomialPartial_single_one (i : Fin 3)
    (F : MvPolynomial (Fin 3) ℝ) :
    directionalPolynomialPartial (Pi.single i 1) F = MvPolynomial.pderiv i F := by
  simp [directionalPolynomialPartial, Pi.single_apply]

theorem stopped_pderiv_nonconstant {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (i : Fin 3) (hM : (fun j => S.2.2 j i) = 0) (c : ℝ) :
    MvPolynomial.pderiv i (coefficientPolynomial S.1) ≠ MvPolynomial.C c := by
  have hh : (Pi.single i (1 : ℝ) : PhysicalSpace) ≠ 0 := by
    intro hz
    have hi := congrFun hz i
    simpa using hi
  have hm : S.2.2 *ᵥ Pi.single i 1 = 0 := by
    simpa only [Matrix.mulVec_single_one] using hM
  simpa only [directionalPolynomialPartial_single_one] using
    stopped_directionalPolynomialPartial_nonconstant hP S hstop (Pi.single i 1) hh hm c

end PaperI
