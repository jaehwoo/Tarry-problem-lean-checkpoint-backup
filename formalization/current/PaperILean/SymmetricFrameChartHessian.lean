import PaperILean.FullFrameSecondVariation
import PaperILean.FrameEnergySmoothness
import PaperILean.DirectionalHessian

/-! Genuine Frechet Hessian in the explicit symmetric exponential coordinates
S ↦ B exp(S). The diagonal estimate is valid at S=0 for every positive B;
in particular it holds at each critical/minimizing frame as in I248,282.
This file does not assert parameter-dependent IFT or smooth minima. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def symmetricFrameParam (B : PositiveFrame) (S : SymmetricMatrix 3) :
    Matrix (Fin 3) (Fin 3) ℝ := B.val * NormedSpace.exp ℝ (S : Matrix (Fin 3) (Fin 3) ℝ)

theorem symmetricFrameParam_det_pos (B : PositiveFrame) (S : SymmetricMatrix 3) :
    0 < (symmetricFrameParam B S).det := by
  simpa only [symmetricFrameParam, recenteredPositiveFrame, one_smul] using
    (recenteredPositiveFrame B (S : Matrix (Fin 3) (Fin 3) ℝ) S.property 1).property

theorem symmetricFrameParam_zero (B : PositiveFrame) : symmetricFrameParam B 0 = B.val := by
  simp [symmetricFrameParam, NormedSpace.exp_zero]

theorem contDiff_symmetricFrameParam (B : PositiveFrame) : ContDiff ℝ ⊤ (symmetricFrameParam B) :=
  contDiff_const.mul (contDiff_matrix_exp.comp (symmetricMatrixIncl 3).contDiff)

def symmetricFrameEnergy {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) (S : SymmetricMatrix 3) : ℝ :=
  FrameEnergy F c lam (symmetricFrameParam B S)

theorem contDiff_symmetricFrameEnergy {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) : ContDiff ℝ ⊤ (symmetricFrameEnergy F c lam B) := by
  apply contDiff_iff_contDiffAt.mpr
  intro S
  exact (contDiffAt_FrameEnergy F c lam
    ⟨symmetricFrameParam B S, symmetricFrameParam_det_pos B S⟩).comp S
      (contDiff_symmetricFrameParam B).contDiffAt

theorem symmetricFrameEnergy_smul_line {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) (H : SymmetricMatrix 3) :
    (fun t : ℝ => symmetricFrameEnergy F c lam B (t • H)) =
      frameEnergyCurve F c lam B (H : Matrix (Fin 3) (Fin 3) ℝ) := rfl

theorem symmetricFrameEnergy_fderiv_eq_zero_of_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    fderiv ℝ (symmetricFrameEnergy F c lam B) 0 = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply IsMinOn.isLocalMin (s := Set.univ) _ Filter.univ_mem
  intro S _
  simpa only [symmetricFrameEnergy, symmetricFrameParam_zero] using
    hB ⟨symmetricFrameParam B S, symmetricFrameParam_det_pos B S⟩

def symmetricFrameEnergyHessian {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) : SymmetricMatrix 3 →L[ℝ] SymmetricMatrix 3 →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (symmetricFrameEnergy F c lam B)) 0

theorem symmetricFrameEnergyHessian_diag_eq {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (H : SymmetricMatrix 3) :
    symmetricFrameEnergyHessian F c lam B H H =
      deriv (deriv (frameEnergyCurve F c lam B (H : Matrix (Fin 3) (Fin 3) ℝ))) 0 :=
  (deriv2_smul_line_eq_fderiv2 _ (contDiff_symmetricFrameEnergy F c lam B) H).symm

theorem symmetricFrameEnergyHessian_diag_formula {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (H : SymmetricMatrix 3) :
    symmetricFrameEnergyHessian F c lam B H H =
      4 * (matrixFullHSNorm (B.val * (H : Matrix (Fin 3) (Fin 3) ℝ))) ^ 2 +
      4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H.val (affineJetTensor F c B.val r))) ^ 2) +
      lam * deriv (deriv (frameLogEnergyCurve B H.val)) 0 := by
  rw [symmetricFrameEnergyHessian_diag_eq, frameEnergyCurve_second_derivative_zero F c lam B H.val H.property]

theorem symmetricFrameEnergyHessian_ge {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame) (H : SymmetricMatrix 3) :
    4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H.val (affineJetTensor F c B.val r))) ^ 2) +
      8 * lam * (matrixFullHSNorm H.val) ^ 2 ≤ symmetricFrameEnergyHessian F c lam B H H := by
  rw [symmetricFrameEnergyHessian_diag_eq]
  exact frameEnergyCurve_second_derivative_ge_tensor F c lam hlam B H.val H.property

theorem symmetricFrameEnergyHessian_pos {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (H : SymmetricMatrix 3) (hne : H ≠ 0) :
    0 < symmetricFrameEnergyHessian F c lam B H H := by
  rw [symmetricFrameEnergyHessian_diag_eq]
  exact frameEnergyCurve_second_derivative_pos F c lam hlam B H.val H.property
    (fun hz => hne (Subtype.ext hz))

theorem symmetricFrameEnergyHessian_injective {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    Function.Injective (symmetricFrameEnergyHessian F c lam B) := by
  intro H K h
  by_contra hne
  have hp := symmetricFrameEnergyHessian_pos F c lam hlam B (H - K) (sub_ne_zero.mpr hne)
  have hz : symmetricFrameEnergyHessian F c lam B (H - K) = 0 := by rw [map_sub, h, sub_self]
  rw [hz, ContinuousLinearMap.zero_apply] at hp
  exact (lt_irrefl 0) hp

theorem source_symmetricFrameEnergyHessian_ge {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R)
    (B : PositiveFrame) (H : SymmetricMatrix 3) :
    4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H.val (affineJetTensor F c B.val r))) ^ 2) +
      8 * sourceRegularization CX C0 R * (matrixFullHSNorm H.val) ^ 2 ≤
        symmetricFrameEnergyHessian F c (sourceRegularization CX C0 R) B H H :=
  symmetricFrameEnergyHessian_ge F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le B H

end PaperI
