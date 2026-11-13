import PaperILean.JointFrameEnergySmoothness
import PaperILean.FrameEnergyMixedDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual first variation in a fixed test generator, jointly smooth in center
and positive frame. Recentring is exact along the same exponential generator;
no commutation between independent directions or eigenvalue separation is used. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def frameFirstVariation {k : ℕ} (F : CoefficientSpace k) (lam : ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ)
    (p : PhysicalSpace × Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  deriv (fun t : ℝ => FrameEnergy F p.1 lam (p.2 * NormedSpace.exp ℝ (t • H))) 0

theorem frameFirstVariation_eq_curve {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    frameFirstVariation F lam H (c, B.val) = deriv (frameEnergyCurve F c lam B H) 0 := rfl

theorem contDiffAt_frameFirstVariation {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiffAt ℝ ⊤ (frameFirstVariation F lam H) (c, B.val) := by
  let f : (PhysicalSpace × Matrix (Fin 3) (Fin 3) ℝ) → ℝ → ℝ :=
    fun p t => FrameEnergy F p.1 lam (p.2 * NormedSpace.exp ℝ (t • H))
  have hm : ContDiff ℝ ⊤ (fun p : (PhysicalSpace × Matrix (Fin 3) (Fin 3) ℝ) × ℝ =>
      ((F, p.1.1), p.1.2 * NormedSpace.exp ℝ (p.2 • H))) :=
    (contDiff_const.prodMk contDiff_fst.fst).prodMk
      (contDiff_fst.snd.mul (contDiff_matrix_exp.comp (contDiff_snd.smul contDiff_const)))
  have hh : ContDiffAt ℝ ⊤ (Function.uncurry f) ((c, B.val), 0) := by
    have hg : ContDiffAt ℝ ⊤
        (fun q : (CoefficientSpace k × PhysicalSpace) × Matrix (Fin 3) (Fin 3) ℝ =>
          FrameEnergy q.1.1 q.1.2 lam q.2)
        ((F, c), B.val * NormedSpace.exp ℝ ((0 : ℝ) • H)) := by
      simpa using contDiffAt_FrameEnergy_joint F c lam B
    exact hg.comp ((c, B.val), (0 : ℝ)) hm.contDiffAt
  have hd : ContDiffAt ℝ ⊤ (fun p => fderiv ℝ (f p) 0) (c, B.val) :=
    hh.fderiv contDiffAt_const (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
  exact hd.clm_apply contDiffAt_const

theorem frameFirstVariation_zero_of_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    frameFirstVariation F lam H (c, B.val) = 0 := by
  rw [frameFirstVariation_eq_curve, frameEnergyCurve_first_derivative_balance F c lam B H hH,
    frameBalanceMatrix_eq_zero_of_minimum F c lam B hB]
  simp

theorem frameEnergyCurve_recenter {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (s t : ℝ) :
    frameEnergyCurve F c lam B H (s + t) =
      frameEnergyCurve F c lam (recenteredPositiveFrame B H hH s) H t := by
  have he : NormedSpace.exp ℝ ((s + t) • H) =
      NormedSpace.exp ℝ (s • H) * NormedSpace.exp ℝ (t • H) := by
    rw [add_smul]
    exact Matrix.exp_add_of_commute ℝ _ _ (((Commute.refl H).smul_left s).smul_right t)
  simp only [frameEnergyCurve, recenteredPositiveFrame, he, Matrix.mul_assoc]

theorem frameFirstVariation_along_exponential {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (s : ℝ) :
    frameFirstVariation F lam H (c, B.val * NormedSpace.exp ℝ (s • H)) =
      deriv (frameEnergyCurve F c lam B H) s := by
  change deriv (frameEnergyCurve F c lam (recenteredPositiveFrame B H hH s) H) 0 = _
  have he : frameEnergyCurve F c lam (recenteredPositiveFrame B H hH s) H =
      fun t => frameEnergyCurve F c lam B H (s + t) :=
    funext (fun t => (frameEnergyCurve_recenter F c lam B H hH s t).symm)
  rw [he, deriv_comp_const_add, add_zero]

theorem fderiv_frameFirstVariation_center {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (h : PhysicalSpace)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    fderiv ℝ (frameFirstVariation F lam H) (c, B.val) (B.val *ᵥ h, 0) =
      4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h H r := by
  have hp : HasDerivAt (fun t : ℝ => (c + t • (B.val *ᵥ h), B.val))
      (B.val *ᵥ h, 0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (B.val *ᵥ h)).const_add c).prodMk
      (hasDerivAt_const 0 B.val)
  have hd := ((contDiffAt_frameFirstVariation F c lam B H).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (frameFirstVariation F lam H)
      (fderiv ℝ (frameFirstVariation F lam H) (c, B.val))
      (c + (0 : ℝ) • (B.val *ᵥ h), B.val) := by simpa using hd
  have hh := hd'.comp_hasDerivAt (0 : ℝ) hp
  have ht := hasDerivAt_frameEnergyCurve_center_firstVariation F c lam B h H hH
  exact hh.unique ht

theorem fderiv_frameFirstVariation_frame_diag {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame) (S : SymmetricMatrix 3) :
    fderiv ℝ (frameFirstVariation F lam S.val) (c, B.val) (0, B.val * S.val) =
      symmetricFrameEnergyHessian F c lam B S S := by
  have hp := (hasDerivAt_const (0 : ℝ) c).prodMk
    (hasDerivAt_frame_exponential_zero B.val S.val)
  have hd := ((contDiffAt_frameFirstVariation F c lam B S.val).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (frameFirstVariation F lam S.val)
      (fderiv ℝ (frameFirstVariation F lam S.val) (c, B.val))
      (c, B.val * NormedSpace.exp ℝ ((0 : ℝ) • S.val)) := by simpa using hd
  have hh := hd'.comp_hasDerivAt (0 : ℝ) hp
  have he : (fun t : ℝ => frameFirstVariation F lam S.val
      (c, B.val * NormedSpace.exp ℝ (t • S.val))) =
      deriv (frameEnergyCurve F c lam B S.val) :=
    funext (frameFirstVariation_along_exponential F c lam B S.val S.property)
  rw [symmetricFrameEnergyHessian_diag_eq]
  simpa only [Function.comp_def, he] using hh.deriv.symm

end PaperI
