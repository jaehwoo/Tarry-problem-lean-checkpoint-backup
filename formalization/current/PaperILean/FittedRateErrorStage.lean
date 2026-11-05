import PaperILean.GramPseudoinverseNorm
import PaperILean.RegularSectionDifferential
import Mathlib.Algebra.BigOperators.Fin

/-! I1448[42,78) and I1450[0,88): the quantitative fitted-versus-actual
body-rate error in every five-column chart. The intrinsic normalization is
the actual omitted body component being one; no coordinate-velocity
normalization is substituted. The literal Gram pseudoinverse, full augmented
derivative and Euclidean norms are retained. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace PaperI.FittedRateErrorStage

open RegularSectionDifferential RegularSectionPseudoinverse GramPseudoinverseNorm

/-- Delete exactly the chosen column in the original generator order. -/
noncomputable def omittedComplement {k : ℕ} (i : Fin 6) (S : AugmentedState k) :
    Matrix (AugmentedCoordinateIndex k) (Fin 5) ℝ :=
  fun r j => augmentedOrbitMatrix k S r (i.succAbove j)

/-- The actual omitted column of the same augmented differential. -/
noncomputable def omittedColumn {k : ℕ} (i : Fin 6) (S : AugmentedState k) :
    AugmentedCoordinateIndex k → ℝ :=
  fun r => augmentedOrbitMatrix k S r i

/-- The five actual body components, with precisely the same deletion. -/
noncomputable def otherBodyRates (i : Fin 6) (ξ : Fin 6 → ℝ) : Fin 5 → ℝ :=
  fun j => ξ (i.succAbove j)

/-- The manuscript's fitted vector using its literal Gram pseudoinverse. -/
noncomputable def fittedRates {k : ℕ} (i : Fin 6) (S : AugmentedState k) :
    Fin 5 → ℝ :=
  -(leftPseudoinverse (omittedComplement i S) *ᵥ omittedColumn i S)

/-- Split the actual augmented action at any normalized omitted body component. -/
theorem orbit_matrix_split {k : ℕ} (i : Fin 6) (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hi : ξ i = 1) :
    augmentedOrbitMatrix k S *ᵥ ξ = omittedColumn i S +
      omittedComplement i S *ᵥ otherBodyRates i ξ := by
  funext r
  change (∑ j : Fin 6, augmentedOrbitMatrix k S r j * ξ j) =
    augmentedOrbitMatrix k S r i +
      ∑ j : Fin 5, augmentedOrbitMatrix k S r (i.succAbove j) * ξ (i.succAbove j)
  simpa only [hi, mul_one] using
    (Fin.sum_univ_succAbove (fun j : Fin 6 => augmentedOrbitMatrix k S r j * ξ j) i)

/-- The exact error is the literal left pseudoinverse applied to the actual
augmented action. Its left-inverse property follows from the retained pivot. -/
theorem fitted_error_eq {k : ℕ} (i : Fin 6) (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hi : ξ i = 1) (τ : ℝ) (hτ : 0 < τ)
    (hσ : τ ≤ descendingSingularValues (omittedComplement i S) (Fin.last 4)) :
    otherBodyRates i ξ - fittedRates i S =
      leftPseudoinverse (omittedComplement i S) *ᵥ (augmentedOrbitMatrix k S *ᵥ ξ) := by
  have hleft := leftPseudoinverse_mul_of_singular_lower (omittedComplement i S) τ hτ hσ
  have h : leftPseudoinverse (omittedComplement i S) *ᵥ
      (augmentedOrbitMatrix k S *ᵥ ξ) =
      leftPseudoinverse (omittedComplement i S) *ᵥ omittedColumn i S + otherBodyRates i ξ := by
    calc
      _ = leftPseudoinverse (omittedComplement i S) *ᵥ
          (omittedColumn i S + omittedComplement i S *ᵥ otherBodyRates i ξ) := by
            rw [orbit_matrix_split i S ξ hi]
      _ = leftPseudoinverse (omittedComplement i S) *ᵥ omittedColumn i S +
          (leftPseudoinverse (omittedComplement i S) * omittedComplement i S) *ᵥ
            otherBodyRates i ξ := by rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      _ = _ := by rw [hleft, Matrix.one_mulVec]
  rw [h, fittedRates]
  abel

/-- The quantitative pivot controls the error with the actual augmented norm. -/
theorem fitted_error_bound {k : ℕ} (i : Fin 6) (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hi : ξ i = 1) (P Cs : ℝ) (hP : 0 < P)
    (hσ : P ^ (-Cs) ≤ descendingSingularValues (omittedComplement i S) (Fin.last 4)) :
    coordinateL2Norm (otherBodyRates i ξ - fittedRates i S) ≤
      P ^ Cs * augmentedStateNorm (augmentedOrbitDifferential k S ξ) := by
  have hτ : 0 < P ^ (-Cs) := Real.rpow_pos_of_pos hP _
  rw [fitted_error_eq i S ξ hi (P ^ (-Cs)) hτ hσ]
  have h := leftPseudoinverse_mulVec_norm_le (omittedComplement i S)
    (P ^ (-Cs)) hτ hσ (augmentedOrbitMatrix k S *ᵥ ξ)
  simpa only [augmentedOrbitMatrix_norm, Real.rpow_neg hP.le, inv_inv] using h

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- Complete quantitative stage I1448[42,78)+I1450[0,88). Every omitted
column is allowed, with the intrinsic normalization imposed on the actual
body velocity. The preparation bound concerns the actual augmented path. -/
theorem fitted_rate_error_stage (k : ℕ) (_hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (i : Fin 6)
    (hi : originalAffineBodyCoordinates (g t) v i = 1)
    (P H Cs Ca : ℝ) (hP : 2 ≤ P) (_hH : 0 < H)
    (hσ : P ^ (-Cs) ≤ descendingSingularValues
      (omittedComplement i (augmentedPullback S0 (g t))) (Fin.last 4))
    (hprepared : augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      P ^ Ca / H) :
    coordinateL2Norm (otherBodyRates i (originalAffineBodyCoordinates (g t) v) -
      fittedRates i (augmentedPullback S0 (g t))) ≤ P ^ (Cs + Ca) / H := by
  have hpos : 0 < P := by linarith
  have h := fitted_error_bound i (augmentedPullback S0 (g t))
    (originalAffineBodyCoordinates (g t) v) hi P Cs hpos hσ
  rw [← (augmentedPullback_hasDerivAt_body S0 g v t hg).deriv] at h
  calc
    _ ≤ P ^ Cs * augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) := h
    _ ≤ P ^ Cs * (P ^ Ca / H) :=
      mul_le_mul_of_nonneg_left hprepared (Real.rpow_nonneg hpos.le Cs)
    _ = P ^ (Cs + Ca) / H := by rw [← mul_div_assoc, ← Real.rpow_add hpos]

end PaperI.FittedRateErrorStage
