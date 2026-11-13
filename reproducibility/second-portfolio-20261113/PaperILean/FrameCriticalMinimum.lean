import PaperILean.SymmetricGramCoordinates
import PaperILean.JointFrameEnergySmoothness
import Mathlib.Analysis.Convex.Deriv

/-! Identify coordinate critical points with global minimizing ellipsoids.
This is not inferred from local IFT alone: actual Gram charts transfer the
derivative, and the already proved geodesic convexity supplies global minimality. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

def positiveSymmetricFrame (B : PositiveFrame) (S : SymmetricMatrix 3) : PositiveFrame :=
  ⟨symmetricFrameParam B S, symmetricFrameParam_det_pos B S⟩

theorem symmetricFrameEnergy_inverse_gram {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B D : PositiveFrame) :
    symmetricFrameEnergy F c lam B (symmetricGramInverse B (symmetricFrameGram D.val)) =
      FrameEnergy F c lam D.val := by
  apply FrameEnergy_eq_of_same_gram F c lam
    (positiveSymmetricFrame B (symmetricGramInverse B (symmetricFrameGram D.val))) D
  have h := symmetricGramCoordinates_inverse B (symmetricFrameGram D.val) (positiveFrame_gram_posDef D)
  rw [symmetricGramCoordinates_eq_frameGram] at h
  exact congrArg Subtype.val h

def symmetricFrameCoordinateChange (B D : PositiveFrame) (S : SymmetricMatrix 3) : SymmetricMatrix 3 :=
  symmetricGramInverse B (symmetricGramCoordinates D S)

theorem contDiff_symmetricFrameCoordinateChange (B D : PositiveFrame) :
    ContDiff ℝ ⊤ (symmetricFrameCoordinateChange B D) := by
  apply contDiff_iff_contDiffAt.mpr
  intro S
  exact (contDiffAt_symmetricGramInverse B _ (symmetricGramCoordinates_posDef D S)).comp S
    (contDiff_symmetricGramCoordinates D).contDiffAt

theorem symmetricFrameEnergy_coordinate_change {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B D : PositiveFrame) (S : SymmetricMatrix 3) :
    symmetricFrameEnergy F c lam B (symmetricFrameCoordinateChange B D S) =
      symmetricFrameEnergy F c lam D S := by
  unfold symmetricFrameCoordinateChange
  rw [symmetricGramCoordinates_eq_frameGram]
  exact symmetricFrameEnergy_inverse_gram F c lam B (positiveSymmetricFrame D S)

theorem symmetricFrameCoordinateChange_param_zero (B : PositiveFrame) (S : SymmetricMatrix 3) :
    symmetricFrameCoordinateChange B (positiveSymmetricFrame B S) 0 = S := by
  unfold symmetricFrameCoordinateChange
  rw [symmetricGramCoordinates_zero]
  change symmetricGramInverse B (symmetricFrameGram (symmetricFrameParam B S)) = S
  rw [← symmetricGramCoordinates_eq_frameGram, symmetricGramInverse_coordinates]

theorem symmetricFrameEnergy_critical_recenter {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (S : SymmetricMatrix 3)
    (hcrit : fderiv ℝ (symmetricFrameEnergy F c lam B) S = 0) :
    fderiv ℝ (symmetricFrameEnergy F c lam (positiveSymmetricFrame B S)) 0 = 0 := by
  let D := positiveSymmetricFrame B S
  have ho : HasFDerivAt (symmetricFrameEnergy F c lam B) (0 : SymmetricMatrix 3 →L[ℝ] ℝ)
      (symmetricFrameCoordinateChange B D 0) := by
    rw [symmetricFrameCoordinateChange_param_zero]
    rw [← hcrit]
    exact ((contDiff_symmetricFrameEnergy F c lam B).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi := ((contDiff_symmetricFrameCoordinateChange B D).differentiable (by simp)).differentiableAt (x := 0) |>.hasFDerivAt
  have h := ho.comp 0 hi
  have he : (fun U => symmetricFrameEnergy F c lam B (symmetricFrameCoordinateChange B D U)) =
      symmetricFrameEnergy F c lam D := by
    funext U
    exact symmetricFrameEnergy_coordinate_change F c lam B D U
  simp only [Function.comp_def] at h
  rw [he] at h
  simpa only [ContinuousLinearMap.zero_comp] using h.fderiv

theorem FrameEnergy_minimum_of_symmetric_critical {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (hcrit : fderiv ℝ (symmetricFrameEnergy F c lam B) 0 = 0) :
    ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val := by
  intro D
  obtain ⟨H, hH, Q, hQ, hdet, hconn⟩ := exists_symmetric_exponential_connection B D
  let K : SymmetricMatrix 3 := symmetricMatrixOf H hH
  have hline : HasDerivAt (fun t : ℝ => t • K) K 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const K
  have hf : HasFDerivAt (symmetricFrameEnergy F c lam B) (0 : SymmetricMatrix 3 →L[ℝ] ℝ)
      ((0 : ℝ) • K) := by
    rw [zero_smul, ← hcrit]
    exact ((contDiff_symmetricFrameEnergy F c lam B).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hd : HasDerivAt (frameEnergyCurve F c lam B H) 0 0 := by
    have h := hf.comp_hasDerivAt 0 hline
    simpa only [zero_smul, hcrit, ContinuousLinearMap.zero_apply, symmetricFrameEnergy_smul_line] using h
  have hs := (frameEnergyCurve_convex F c lam hlam B H hH).le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num) hd
  have he1 : frameEnergyCurve F c lam B H 1 = FrameEnergy F c lam D.val := by
    simp only [frameEnergyCurve, one_smul]
    rw [hconn, FrameEnergy_right_specialOrthogonal F c lam _ Q hQ hdet]
  simpa only [slope_def_field, sub_zero, div_one, frameEnergyCurve_at_zero, he1, sub_nonneg] using hs

theorem FrameEnergy_minimum_of_coordinate_critical {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) (S : SymmetricMatrix 3)
    (hcrit : fderiv ℝ (symmetricFrameEnergy F c lam B) S = 0) :
    ∀ D : PositiveFrame, FrameEnergy F c lam (symmetricFrameParam B S) ≤ FrameEnergy F c lam D.val :=
  FrameEnergy_minimum_of_symmetric_critical F c lam hlam (positiveSymmetricFrame B S)
    (symmetricFrameEnergy_critical_recenter F c lam B S hcrit)

end PaperI
