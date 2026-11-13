import PaperILean.SymmetricCongruence
import PaperILean.SymmetricFrameChartHessian

/-! The exact symmetric coordinates required at I227,248. In fact this is
a global analytic parametrization of the open positive symmetric cone.
Its frame representative is exactly B exp S; the Gram is B exp(2S) B^T. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm Topology
namespace PaperI

def symmetricGramCoordinates (B : PositiveFrame) (S : SymmetricMatrix 3) : SymmetricMatrix 3 :=
  symmetricCongruence B.val (symmetricMatrixExp ((2 : ℝ) • S))

def symmetricGramInverse (B : PositiveFrame) (Q : SymmetricMatrix 3) : SymmetricMatrix 3 :=
  (1 / 2 : ℝ) • symmetricMatrixLog (symmetricCongruence B.val⁻¹ Q)

theorem symmetricGramCoordinates_coe (B : PositiveFrame) (S : SymmetricMatrix 3) :
    (symmetricGramCoordinates B S).val = B.val * NormedSpace.exp ℝ ((2 : ℝ) • S.val) * B.valᵀ := rfl

theorem symmetricGramInverse_coe (B : PositiveFrame) (Q : SymmetricMatrix 3) :
    (symmetricGramInverse B Q).val = (1 / 2 : ℝ) • CFC.log (B.val⁻¹ * Q.val * B.val⁻¹ᵀ) := rfl

theorem symmetricGramCoordinates_posDef (B : PositiveFrame) (S : SymmetricMatrix 3) :
    (symmetricGramCoordinates B S).val.PosDef :=
  symmetricCongruence_posDef B.val (positiveFrame_isUnit B) _ (symmetricMatrixExp_posDef _)

theorem symmetricGramInverse_coordinates (B : PositiveFrame) (S : SymmetricMatrix 3) :
    symmetricGramInverse B (symmetricGramCoordinates B S) = S := by
  unfold symmetricGramInverse symmetricGramCoordinates
  rw [symmetricCongruence_inv_left _ (positiveFrame_isUnit B), symmetricMatrixLog_exp, smul_smul]
  norm_num

theorem symmetricGramCoordinates_inverse (B : PositiveFrame) (Q : SymmetricMatrix 3)
    (hQ : Q.val.PosDef) : symmetricGramCoordinates B (symmetricGramInverse B Q) = Q := by
  have hBi : IsUnit B.val⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr (positiveFrame_isUnit B)
  unfold symmetricGramCoordinates symmetricGramInverse
  rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    symmetricMatrixExp_log _ (symmetricCongruence_posDef B.val⁻¹ hBi Q hQ),
    symmetricCongruence_inv_right _ (positiveFrame_isUnit B)]

theorem symmetricGramCoordinates_eq_frameGram (B : PositiveFrame) (S : SymmetricMatrix 3) :
    symmetricGramCoordinates B S = symmetricFrameGram (symmetricFrameParam B S) := by
  apply Subtype.ext
  exact (by
    simpa only [symmetricGramCoordinates_coe, symmetricFrameGram, symmetricMatrixOf,
      symmetricFrameParam, one_smul, mul_one] using
      (symmetric_frame_exponential_gram B.val S.val S.property 1).symm)

theorem symmetricGramCoordinates_zero (B : PositiveFrame) :
    symmetricGramCoordinates B 0 = symmetricFrameGram B.val := by
  rw [symmetricGramCoordinates_eq_frameGram, symmetricFrameParam_zero]

theorem symmetricGramInverse_frameGram (B : PositiveFrame) :
    symmetricGramInverse B (symmetricFrameGram B.val) = 0 := by
  rw [← symmetricGramCoordinates_zero, symmetricGramInverse_coordinates]

theorem contDiff_symmetricGramCoordinates (B : PositiveFrame) :
    ContDiff ℝ ⊤ (symmetricGramCoordinates B) :=
  (contDiff_symmetricCongruence B.val).comp
    (contDiff_symmetricMatrixExp.comp (contDiff_const.smul contDiff_id))

theorem contDiffAt_symmetricGramInverse (B : PositiveFrame) (Q : SymmetricMatrix 3)
    (hQ : Q.val.PosDef) : ContDiffAt ℝ ⊤ (symmetricGramInverse B) Q := by
  have hBi : IsUnit B.val⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr (positiveFrame_isUnit B)
  exact contDiffAt_const.smul ((contDiffAt_symmetricMatrixLog _
    (symmetricCongruence_posDef B.val⁻¹ hBi Q hQ)).comp Q
      (contDiff_symmetricCongruence B.val⁻¹).contDiffAt)

def symmetricGramChart (B : PositiveFrame) : PartialHomeomorph (SymmetricMatrix 3) (SymmetricMatrix 3) where
  toFun := symmetricGramCoordinates B
  invFun := symmetricGramInverse B
  source := Set.univ
  target := positiveSymmetricCone 3
  map_source' := fun S _ => symmetricGramCoordinates_posDef B S
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun S _ => symmetricGramInverse_coordinates B S
  right_inv' := fun Q hQ => symmetricGramCoordinates_inverse B Q hQ
  open_source := isOpen_univ
  open_target := isOpen_positiveSymmetricCone 3
  continuousOn_toFun := (contDiff_symmetricGramCoordinates B).continuous.continuousOn
  continuousOn_invFun := fun Q hQ => (contDiffAt_symmetricGramInverse B Q hQ).continuousAt.continuousWithinAt

theorem symmetricGramChart_source (B : PositiveFrame) : (symmetricGramChart B).source = Set.univ := rfl

theorem symmetricGramChart_target (B : PositiveFrame) :
    (symmetricGramChart B).target = positiveSymmetricCone 3 := rfl

theorem symmetricGramChart_target_mem_nhds (B : PositiveFrame) :
    (symmetricGramChart B).target ∈ 𝓝 (symmetricFrameGram B.val) :=
  (isOpen_positiveSymmetricCone 3).mem_nhds (positiveFrame_gram_posDef B)

theorem symmetricGramChart_zero (B : PositiveFrame) :
    symmetricGramChart B 0 = symmetricFrameGram B.val := symmetricGramCoordinates_zero B

end PaperI
