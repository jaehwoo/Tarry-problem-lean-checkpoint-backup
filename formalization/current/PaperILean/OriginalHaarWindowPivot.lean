import PaperILean.AugmentedOrbit

/-! Exact Euclidean-to-coordinate application of the source physical pivot.
The Lie action differentiates the polynomial before discarding its constant.
No augmented or spatial pivot replaces the source phase-only physical pivot. -/
noncomputable section
namespace PaperI
open scoped BigOperators

/-- Euclidean norm is bounded by the sum of the absolute coordinates, with
no factor depending on a chosen frame or the vector itself. -/
theorem originalHaar_coordinateL2Norm_le_sum_abs
    {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    coordinateL2Norm v ≤ ∑ i, |v i| := by
  have hsum : (∑ i, (v i)^2) ≤ (∑ i, |v i|)^2 := by
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset ι)) (f := fun i => |v i|)
        (fun i _ => abs_nonneg (v i)))
  have hnonneg : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hn := coordinateL2Norm_nonneg v
  rw [← coordinateL2Norm_sq] at hsum
  nlinarith

/-- This is the literal quotient physical Lie action `[XJ]`. -/
def originalHaarPhysicalLieAction {k : ℕ} (J : CoefficientSpace k)
    (v : Fin 6 → ℝ) : CoefficientSpace k :=
  affineFieldCoefficientMap k (upperAffineFieldTranslation v) (upperAffineFieldLinear v) J

/-- An original physical Euclidean lower bound and the actual quotient
orbit derivative identity give the scalar majorant used in the path proof.
The derivative identity is retained explicitly until the actual orbit-chain
rule theorem is instantiated; it is not a published-input contract. -/
theorem originalHaar_physical_pivot_body_majorant
    {k : ℕ} (J q' : CoefficientSpace k) (v : Fin 6 → ℝ) (H : ℝ)
    (hH : 0 ≤ H)
    (hpivot : coordinateL2Norm v ≤ H*coefficientEuclideanNorm
      (originalHaarPhysicalLieAction J v))
    (hactual : q' = originalHaarPhysicalLieAction J v) :
    ∀ i : Fin 6, |v i| ≤ H*∑ α, |q' α| := by
  intro i
  have hi : |v i| ≤ coordinateL2Norm v := abs_le_sqrt_sum_sq v i
  have hcoeff : coefficientEuclideanNorm q' ≤ ∑ α, |q' α| :=
    originalHaar_coordinateL2Norm_le_sum_abs q'
  rw [← hactual] at hpivot
  exact hi.trans (hpivot.trans (mul_le_mul_of_nonneg_left hcoeff hH))

/-- The source coefficient Euclidean bound controls every actual quotient
coordinate; the arbitrary constant representative is never included. -/
theorem originalHaar_coefficient_coordinate_bound {k : ℕ}
    (J : CoefficientSpace k) (B : ℝ) (hJ : coefficientEuclideanNorm J ≤ B)
    (α : MonomialIndex k) : |J α| ≤ B :=
  (abs_le_sqrt_sum_sq J α).trans hJ

end PaperI
