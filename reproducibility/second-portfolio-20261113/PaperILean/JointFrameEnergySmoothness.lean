import PaperILean.JointPolynomialSmoothness
import PaperILean.SymmetricFrameHessianInvertible

/-! Joint coefficient/center/symmetric-frame regularity of the unchanged energy.
All real lambda are allowed for regularity; positivity is used only by the
already checked Hessian equivalence, not silently added here. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

set_option maxHeartbeats 600000

theorem contDiffAt_FrameEnergy_joint {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    ContDiffAt ℝ ⊤ (fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ =>
      FrameEnergy p.1.1 p.1.2 lam p.2) ((F, c), B.val) := by
  have hs : ContDiffAt ℝ ⊤
      (fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ => p.2)
      ((F, c), B.val) := contDiffAt_snd
  have hl : ContDiffAt ℝ ⊤
      (fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ =>
        sourceMatrixLogEnergy (p.2 * p.2ᵀ)) ((F, c), B.val) :=
    ContDiffAt.comp (f := fun p : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ => p.2)
      (g := fun C : Matrix (Fin 3) (Fin 3) ℝ => sourceMatrixLogEnergy (C * Cᵀ))
      ((F, c), B.val) (contDiffAt_frameLogEnergy B) hs
  unfold FrameEnergy
  exact (((contDiff_matrixFullHSNorm_sq.comp contDiff_snd).contDiffAt.add
    (ContDiff.sum (fun r _ => contDiff_jetTensorHSNorm_sq_joint r)).contDiffAt).sub
      (contDiffAt_const.mul (((contDiff_matrix_det_three.comp contDiff_snd).contDiffAt
        (x := ((F, c), B.val))).log
        B.property.ne'))).add
          (contDiffAt_const.mul hl)

theorem contDiff_symmetricFrameEnergy_joint {k : ℕ} (lam : ℝ) (B : PositiveFrame) :
    ContDiff ℝ ⊤ (fun p : (CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3 =>
      symmetricFrameEnergy p.1.1 p.1.2 lam B p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (contDiffAt_FrameEnergy_joint p.1.1 p.1.2 lam
    ⟨symmetricFrameParam B p.2, symmetricFrameParam_det_pos B p.2⟩).comp p
      (contDiff_fst.prodMk ((contDiff_symmetricFrameParam B).comp contDiff_snd)).contDiffAt

theorem contDiff_infty_symmetricFrameEnergy_joint {k : ℕ} (lam : ℝ) (B : PositiveFrame) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3 =>
        symmetricFrameEnergy p.1.1 p.1.2 lam B p.2) :=
  (contDiff_symmetricFrameEnergy_joint lam B).of_le le_top

def symmetricFrameGradient {k : ℕ} (lam : ℝ) (B : PositiveFrame)
    (p : (CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3) : SymmetricMatrix 3 →L[ℝ] ℝ :=
  fderiv ℝ (symmetricFrameEnergy p.1.1 p.1.2 lam B) p.2

theorem symmetricFrameGradient_apply {k : ℕ} (lam : ℝ) (B : PositiveFrame)
    (F : CoefficientSpace k) (c : PhysicalSpace) (S : SymmetricMatrix 3) :
    symmetricFrameGradient lam B ((F, c), S) = fderiv ℝ (symmetricFrameEnergy F c lam B) S := rfl

theorem contDiff_symmetricFrameGradient {k : ℕ} (lam : ℝ) (B : PositiveFrame) :
    ContDiff ℝ ⊤ (symmetricFrameGradient (k := k) lam B) := by
  unfold symmetricFrameGradient
  let f : ((CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3) → SymmetricMatrix 3 → ℝ :=
    fun p S => symmetricFrameEnergy p.1.1 p.1.2 lam B S
  have hm : ContDiff ℝ ⊤
      (fun p : ((CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3) × SymmetricMatrix 3 =>
        (p.1.1, p.2)) := contDiff_fst.fst.prodMk contDiff_snd
  have hp := (contDiff_symmetricFrameEnergy_joint (k := k) lam B).comp hm
  have hh : ContDiff ℝ ⊤ (Function.uncurry f) := hp
  exact ContDiff.fderiv (𝕜 := ℝ)
    (E := (CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3)
    (F := SymmetricMatrix 3) (G := ℝ) (m := ⊤) (n := ⊤) (f := f)
    (g := fun p : (CoefficientSpace k × PhysicalSpace) × SymmetricMatrix 3 => p.2)
    hh contDiff_snd (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)

theorem symmetricFrameGradient_zero_of_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    symmetricFrameGradient lam B ((F, c), 0) = 0 :=
  symmetricFrameEnergy_fderiv_eq_zero_of_minimum F c lam B hB

theorem symmetricFrameGradient_frame_derivative {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) :
    fderiv ℝ (fun S => symmetricFrameGradient lam B ((F, c), S)) 0 =
      symmetricFrameEnergyHessian F c lam B := rfl

theorem symmetricFrameGradient_frame_hasStrictFDerivAt {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame) :
    HasStrictFDerivAt (fun S => symmetricFrameGradient lam B ((F, c), S))
      (symmetricFrameEnergyHessianEquiv F c lam hlam B :
        SymmetricMatrix 3 →L[ℝ] SymmetricMatrix 3 →L[ℝ] ℝ) 0 :=
  symmetricFrameEnergy_gradient_hasStrictFDerivAt F c lam hlam B

end PaperI
