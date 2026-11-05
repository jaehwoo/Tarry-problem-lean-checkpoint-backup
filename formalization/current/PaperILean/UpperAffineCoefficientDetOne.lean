import PaperILean.OriginalUpperNormalPullback
import PaperILean.GeneralAffineCharacter

/-! I440: specialize the signed affine coefficient determinant to the exact
six upper-affine coordinates from I437. The degree may be zero. -/
noncomputable section
namespace PaperI

theorem originalUpperAffineCoefficient_det_one (k : ℕ) (g : Fin 6 → ℝ) :
    LinearMap.det (affineCoefficientMap k ![g 2,g 4,g 5]
      (originalUpperLinearMatrix g)) = 1 := by
  rw [affineCoefficientMap_det]
  simp [originalUpperLinearMatrix, Matrix.det_fin_three]

end PaperI
