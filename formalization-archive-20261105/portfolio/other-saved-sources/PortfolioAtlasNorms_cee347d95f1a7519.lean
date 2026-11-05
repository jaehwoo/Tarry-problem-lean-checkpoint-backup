import PaperILean.ProjectedNormalizationRightFactors
import PaperILean.ExceptionalFiberPackingStage

/-! The Euclidean homogeneous bounds are converted to the literal relative
neighborhood in I303-I305. The fixed dimension loss is made explicit. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm
namespace PaperI.PortfolioAtlasNorms

open ProjectedNormalizationRightFactors ExceptionalFiberPackingStage

theorem entry_le_operator (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    |A i j| ≤ ‖A‖ := by
  let x : EuclideanSpace ℝ (Fin 4) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm (Pi.single j 1)
  have hx : ‖x‖ = 1 := by
    simp [x, EuclideanSpace.norm_eq, Pi.single_apply]
  have hmul := Matrix.l2_opNorm_mulVec A x
  have hi := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 4) ℝ).symm (A *ᵥ x)) i
  have hentry : |A i j| ≤
      ‖(EuclideanSpace.equiv (Fin 4) ℝ).symm (A *ᵥ x)‖ := by
    simpa [x, Matrix.mulVec_single_one, Real.norm_eq_abs] using hi
  exact hentry.trans (by simpa only [hx, mul_one] using hmul)

theorem fullHS_le_operator (A : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixFullHSNorm A ≤ 4 * ‖A‖ := by
  have h := coordinateL2Norm_le_of_component_bound
    (fun p : Fin 4 × Fin 4 => A p.1 p.2) ‖A‖ (norm_nonneg _)
    (fun p => entry_le_operator A p.1 p.2)
  simpa [matrixFullHSNorm] using h

/-- The exponent includes only the fixed loss from four-dimensional Euclidean
operator norm to the sum of the two homogeneous Hilbert--Schmidt norms. -/
theorem relative_radius_of_homogeneous_bounds
    (C P : ℝ) (hP : 2 ≤ P) (a b : Fin 6 → ℝ)
    (hf : ‖homogeneous (originalUpperRelativeFrame a b)‖ ≤ P ^ (4 * C))
    (hi : ‖homogeneous (originalUpperAffineInv (originalUpperRelativeFrame a b))‖ ≤
      P ^ (4 * C)) :
    relativeNeighborhoodRadius a b ≤ P ^ (4 * max C 0 + 3) := by
  have hPpos : 0 < P := by linarith
  have hPone : 1 ≤ P := by linarith
  have hsum : matrixFullHSNorm
        ((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b) +
      matrixFullHSNorm
        (((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b)⁻¹) ≤
      8 * P ^ (4 * C) := by
    rw [originalAffineHomogeneousMatrix_relative, originalAffineHomogeneousMatrix_inverse]
    change matrixFullHSNorm (homogeneous (originalUpperRelativeFrame a b)) +
      matrixFullHSNorm
        (homogeneous (originalUpperAffineInv (originalUpperRelativeFrame a b))) ≤ _
    have h1 := (fullHS_le_operator _).trans (mul_le_mul_of_nonneg_left hf (by norm_num))
    have h2 := (fullHS_le_operator _).trans (mul_le_mul_of_nonneg_left hi (by norm_num))
    linarith
  have hpow : P ^ (4 * C) ≤ P ^ (4 * max C 0) :=
    Real.rpow_le_rpow_of_exponent_le hPone (by nlinarith [le_max_left C 0])
  have hthree : (8 : ℝ) ≤ P ^ (3 : ℝ) := by
    rw [Real.rpow_natCast]
    nlinarith [sq_nonneg (P - 2), mul_nonneg (sub_nonneg.mpr hP) (sq_nonneg P)]
  have hscale : 8 * P ^ (4 * C) ≤ P ^ (4 * max C 0 + 3) := by
    rw [Real.rpow_add hPpos]
    calc
      8 * P ^ (4 * C) ≤ P ^ (3 : ℝ) * P ^ (4 * max C 0) :=
        mul_le_mul hthree hpow (Real.rpow_nonneg hPpos.le _) (by positivity)
      _ = _ := by ring
  exact ExceptionalPackingBounds.literal_relative_neighborhood_le a b _ (hsum.trans hscale)

theorem packing_radius_ge_two (C P : ℝ) (hP : 2 ≤ P) :
    2 ≤ P ^ (4 * max C 0 + 3) := by
  apply hP.trans
  have h : (1 : ℝ) ≤ 4 * max C 0 + 3 := by nlinarith [le_max_right C 0]
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ P) h

end PaperI.PortfolioAtlasNorms
