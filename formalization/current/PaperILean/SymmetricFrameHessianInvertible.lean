import PaperILean.SymmetricFrameChartHessian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Symmetry and actual continuous-linear invertibility of the frame Hessian.
The equivalence is constructed from the proved derivative, not assumed.
Parameter-dependent implicit-function and minimizer selection remain separate. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem symmetricFrameEnergyHessian_symm {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (H K : SymmetricMatrix 3) :
    symmetricFrameEnergyHessian F c lam B H K = symmetricFrameEnergyHessian F c lam B K H :=
  ((contDiff_symmetricFrameEnergy F c lam B).contDiffAt.isSymmSndFDerivAt (by simp)).eq H K

theorem symmetricMatrix_dual_finrank (n : ℕ) :
    Module.finrank ℝ (SymmetricMatrix n) =
      Module.finrank ℝ (SymmetricMatrix n →L[ℝ] ℝ) := by
  calc
    Module.finrank ℝ (SymmetricMatrix n) = Module.finrank ℝ (Module.Dual ℝ (SymmetricMatrix n)) :=
      (Subspace.dual_finrank_eq (K := ℝ) (V := SymmetricMatrix n)).symm
    _ = Module.finrank ℝ (SymmetricMatrix n →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap :
        (SymmetricMatrix n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (SymmetricMatrix n →L[ℝ] ℝ)).finrank_eq

theorem symmetricFrameEnergyHessian_bijective {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    Function.Bijective (symmetricFrameEnergyHessian F c lam B) := by
  have hi := symmetricFrameEnergyHessian_injective F c lam hlam B
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℝ) (V := SymmetricMatrix 3) (V₂ := SymmetricMatrix 3 →L[ℝ] ℝ)
    (symmetricMatrix_dual_finrank 3) (f := (symmetricFrameEnergyHessian F c lam B).toLinearMap)).mp hi

def symmetricFrameEnergyHessianEquiv {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    SymmetricMatrix 3 ≃L[ℝ] (SymmetricMatrix 3 →L[ℝ] ℝ) :=
  let e : SymmetricMatrix 3 ≃ₗ[ℝ] (SymmetricMatrix 3 →L[ℝ] ℝ) :=
    LinearEquiv.ofBijective (symmetricFrameEnergyHessian F c lam B).toLinearMap
      (symmetricFrameEnergyHessian_bijective F c lam hlam B)
  LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := SymmetricMatrix 3)
    (F := SymmetricMatrix 3 →L[ℝ] ℝ) e

theorem symmetricFrameEnergyHessianEquiv_coe {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    (symmetricFrameEnergyHessianEquiv F c lam hlam B :
      SymmetricMatrix 3 →L[ℝ] SymmetricMatrix 3 →L[ℝ] ℝ) =
      symmetricFrameEnergyHessian F c lam B := rfl

theorem symmetricFrameEnergy_gradient_hasStrictFDerivAt {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    HasStrictFDerivAt (fderiv ℝ (symmetricFrameEnergy F c lam B))
      (symmetricFrameEnergyHessianEquiv F c lam hlam B :
        SymmetricMatrix 3 →L[ℝ] SymmetricMatrix 3 →L[ℝ] ℝ) 0 := by
  have h : ContDiff ℝ ⊤ (fderiv ℝ (symmetricFrameEnergy F c lam B)) :=
    (contDiff_symmetricFrameEnergy F c lam B).fderiv_right (by simp)
  rw [symmetricFrameEnergyHessianEquiv_coe]
  exact h.contDiffAt.hasStrictFDerivAt (by simp)

end PaperI
