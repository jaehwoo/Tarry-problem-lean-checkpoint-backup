import PaperILean.NormalColumnRepresentation

/-! The exact simultaneous augmented-kernel pair from I685--693. The scalar
multipliers L and N are affine in y,z. Phase constants are retained until the
subtraction is performed; physical constants are never discarded. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def pairYCoordinates (v : Fin 3 → ℝ) : Fin 6 → ℝ :=
  normalCoordinates v + Pi.single 4 1

def pairZCoordinates (w : Fin 3 → ℝ) : Fin 6 → ℝ :=
  normalCoordinates w + Pi.single 3 1

theorem affineFieldPolynomialMap_pairY (v : Fin 3 → ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap (upperAffineFieldTranslation (pairYCoordinates v))
      (upperAffineFieldLinear (pairYCoordinates v)) F =
      normalScalarPolynomial v * MvPolynomial.pderiv 0 F + MvPolynomial.pderiv 1 F := by
  simp [affineFieldPolynomialMap_apply, pairYCoordinates, normalCoordinates,
    upperAffineFieldTranslation, upperAffineFieldLinear, affineCoordinate,
    Fin.sum_univ_succ, normalScalarPolynomial, add_assoc]

theorem affineFieldPolynomialMap_pairZ (w : Fin 3 → ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap (upperAffineFieldTranslation (pairZCoordinates w))
      (upperAffineFieldLinear (pairZCoordinates w)) F =
      normalScalarPolynomial w * MvPolynomial.pderiv 0 F +
        MvPolynomial.X 2 * MvPolynomial.pderiv 1 F := by
  simp [affineFieldPolynomialMap_apply, pairZCoordinates, normalCoordinates,
    upperAffineFieldTranslation, upperAffineFieldLinear, affineCoordinate,
    Fin.sum_univ_succ, normalScalarPolynomial, add_assoc]

theorem augmentedOrbit_kernel_phase_constant {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hz : augmentedOrbitDifferential k S ξ = 0) :
    ∃ c : ℝ, affineFieldPolynomialMap (upperAffineFieldTranslation ξ)
      (upperAffineFieldLinear ξ) (coefficientPolynomial S.1) = MvPolynomial.C c := by
  refine ⟨MvPolynomial.coeff 0 (affineFieldPolynomialMap
    (upperAffineFieldTranslation ξ) (upperAffineFieldLinear ξ) (coefficientPolynomial S.1)), ?_⟩
  have h := polynomial_affineFieldCoefficientMap (upperAffineFieldTranslation ξ)
    (upperAffineFieldLinear ξ) S.1
  have hp := congrArg Prod.fst hz
  change affineFieldCoefficientMap k _ _ S.1 = 0 at hp
  rw [hp] at h
  have hzero : coefficientPolynomial (0 : CoefficientSpace k) = 0 := by
    simp [coefficientPolynomial]
  rw [hzero] at h
  exact sub_eq_zero.mp h.symm

theorem augmentedOrbit_kernel_physical_polynomial {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hz : augmentedOrbitDifferential k S ξ = 0) (i : Fin 3) :
    affineFieldPolynomialMap (upperAffineFieldTranslation ξ) (upperAffineFieldLinear ξ)
      (affineCoordinate S.2.1 S.2.2 i) = 0 := by
  rw [affineFieldPolynomialMap_affineCoordinate]
  have hp := congrArg Prod.snd hz
  change physicalAffineFieldAction S.2 _ _ = 0 at hp
  have h := congrArg (fun ell : PhysicalAffineData => affineCoordinate ell.1 ell.2 i) hp
  simpa [physicalAffineFieldAction, affineCoordinate] using h

theorem simultaneous_kernel_pair_phase {k : ℕ} (S : AugmentedState k)
    (v w : Fin 3 → ℝ)
    (hY : augmentedOrbitDifferential k S (pairYCoordinates v) = 0)
    (hZ : augmentedOrbitDifferential k S (pairZCoordinates w) = 0) :
    ∃ c0 c1 : ℝ,
      (normalScalarPolynomial w - MvPolynomial.X 2 * normalScalarPolynomial v) *
        MvPolynomial.pderiv 0 (coefficientPolynomial S.1) =
          MvPolynomial.C c0 - MvPolynomial.C c1 * MvPolynomial.X 2 := by
  obtain ⟨c1, hc1⟩ := augmentedOrbit_kernel_phase_constant S _ hY
  obtain ⟨c0, hc0⟩ := augmentedOrbit_kernel_phase_constant S _ hZ
  rw [affineFieldPolynomialMap_pairY] at hc1
  rw [affineFieldPolynomialMap_pairZ] at hc0
  refine ⟨c0, c1, ?_⟩
  rw [← hc0, ← hc1]
  ring

theorem simultaneous_kernel_pair_physical {k : ℕ} (S : AugmentedState k)
    (v w : Fin 3 → ℝ)
    (hY : augmentedOrbitDifferential k S (pairYCoordinates v) = 0)
    (hZ : augmentedOrbitDifferential k S (pairZCoordinates w) = 0) (i : Fin 3) :
    (normalScalarPolynomial w - MvPolynomial.X 2 * normalScalarPolynomial v) *
      MvPolynomial.C (S.2.2 i 0) = 0 := by
  have hc1 := augmentedOrbit_kernel_physical_polynomial S _ hY i
  have hc0 := augmentedOrbit_kernel_physical_polynomial S _ hZ i
  rw [affineFieldPolynomialMap_pairY, pderiv_affineCoordinate,
    pderiv_affineCoordinate] at hc1
  rw [affineFieldPolynomialMap_pairZ, pderiv_affineCoordinate,
    pderiv_affineCoordinate] at hc0
  calc
    _ = (normalScalarPolynomial w * MvPolynomial.C (S.2.2 i 0) +
        MvPolynomial.X 2 * MvPolynomial.C (S.2.2 i 1)) -
        MvPolynomial.X 2 * (normalScalarPolynomial v * MvPolynomial.C (S.2.2 i 0) +
          MvPolynomial.C (S.2.2 i 1)) := by ring
    _ = 0 := by rw [hc0, hc1]; ring

theorem pairYCoordinates_of_constant (v : Fin 3 → ℝ) (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) :
    pairYCoordinates v = upperAffineTranslationCoordinates ![v 2, 1, 0] := by
  ext i
  fin_cases i <;> simp [pairYCoordinates, normalCoordinates,
    upperAffineTranslationCoordinates, hv0, hv1]

end PaperI
