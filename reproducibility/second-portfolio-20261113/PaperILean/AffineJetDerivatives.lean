import PaperILean.AffinePullback
import PaperILean.IteratedPolynomialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Actual affine derivative tensors on the full parent space.

For the normalized pullback only positive orders agree with the original
derivative tensor. At order zero the subtracted constant matters. The linear
and higher chain rules hold for every matrix, including singular matrices.
No Euclidean/HS norm assertion or coefficient-window bound is made here.
-/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

def frameLinearMap (B : Matrix (Fin 3) (Fin 3) ℝ) :
    PhysicalSpace →L[ℝ] PhysicalSpace :=
  ContinuousLinearMap.pi (fun i => ∑ j, B i j • ContinuousLinearMap.proj j)

theorem frameLinearMap_apply (B : Matrix (Fin 3) (Fin 3) ℝ) (v : PhysicalSpace) :
    frameLinearMap B v = B *ᵥ v := by
  ext i
  simp [frameLinearMap, Matrix.mulVec, dotProduct]

theorem affinePoint_eq_frame (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : PhysicalSpace) : affinePoint c B x = c + frameLinearMap B x := by
  rw [frameLinearMap_apply]
  rfl

theorem affinePoint_zero (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    affinePoint c B 0 = c := by
  rw [affinePoint_eq_frame]
  simp

theorem hasFDerivAt_affinePoint (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (x : PhysicalSpace) : HasFDerivAt (affinePoint c B) (frameLinearMap B) x := by
  have heq : affinePoint c B = fun y => c + frameLinearMap B y := by
    funext y
    exact affinePoint_eq_frame c B y
  rw [heq]
  simpa using (hasFDerivAt_const c x).add (frameLinearMap B).hasFDerivAt

theorem hasFDerivAt_phase_affine (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (x : PhysicalSpace) :
    HasFDerivAt (phase (affineCoefficientMap k c B F))
      ((polynomialDifferential (coefficientPolynomial F) (affinePoint c B x)).comp
        (frameLinearMap B)) x := by
  have heq : phase (affineCoefficientMap k c B F) =
      fun y => phase F (affinePoint c B y) - phase F c := by
    funext y
    exact phase_affineCoefficientMap k c B F y
  rw [heq]
  simpa using ((hasFDerivAt_phase F (affinePoint c B x)).comp x
    (hasFDerivAt_affinePoint c B x)).sub (hasFDerivAt_const (phase F c) x)

theorem fderiv_phase_affine_apply (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (x v : PhysicalSpace) :
    fderiv ℝ (phase (affineCoefficientMap k c B F)) x v =
      ∑ i, MvPolynomial.eval (affinePoint c B x)
        (MvPolynomial.pderiv i (coefficientPolynomial F)) * (B *ᵥ v) i := by
  rw [(hasFDerivAt_phase_affine k c B F x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, frameLinearMap_apply,
    polynomialDifferential_apply]

def phaseCoordinateGradient {k : ℕ} (F : CoefficientSpace k) (x : PhysicalSpace) :
    PhysicalSpace :=
  fun i => MvPolynomial.eval x (MvPolynomial.pderiv i (coefficientPolynomial F))

theorem phaseCoordinateGradient_eq_fderiv {k : ℕ} (F : CoefficientSpace k)
    (x : PhysicalSpace) (i : Fin 3) :
    phaseCoordinateGradient F x i = fderiv ℝ (phase F) x (Pi.single i (1 : ℝ)) := by
  simpa only [phaseCoordinateGradient, eval_coefficientPolynomial] using
    (fderiv_evalPolynomial_single (coefficientPolynomial F) x i).symm

theorem phaseCoordinateGradient_affine (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) :
    phaseCoordinateGradient (affineCoefficientMap k c B F) 0 =
      B.transpose *ᵥ phaseCoordinateGradient F c := by
  ext j
  rw [phaseCoordinateGradient_eq_fderiv, fderiv_phase_affine_apply, affinePoint_zero]
  simp [phaseCoordinateGradient, Matrix.mulVec, dotProduct, Pi.single_apply,
    Matrix.transpose_apply, mul_comm]

theorem contDiff_phase_affine_raw (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x => phase F (affinePoint c B x)) := by
  have heq : (fun x => phase F (affinePoint c B x)) =
      (fun y : PhysicalSpace => phase F (c + y)) ∘ frameLinearMap B := by
    funext x
    rw [affinePoint_eq_frame]
    rfl
  rw [heq]
  exact ((contDiff_phase F n).comp (contDiff_const.add contDiff_id)).comp_continuousLinearMap

theorem iteratedFDeriv_phase_affine_raw (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (n : ℕ) (x : PhysicalSpace) :
    iteratedFDeriv ℝ n (fun y => phase F (affinePoint c B y)) x =
      (iteratedFDeriv ℝ n (phase F) (affinePoint c B x)).compContinuousLinearMap
        (fun _ => frameLinearMap B) := by
  have heq : (fun y => phase F (affinePoint c B y)) =
      (fun y : PhysicalSpace => phase F (c + y)) ∘ frameLinearMap B := by
    funext y
    rw [affinePoint_eq_frame]
    rfl
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun y : PhysicalSpace => phase F (c + y)) :=
    (contDiff_phase F (n : WithTop ℕ∞)).comp (contDiff_const.add contDiff_id)
  rw [heq, (frameLinearMap B).iteratedFDeriv_comp_right (i := n) hc x le_rfl,
    iteratedFDeriv_comp_add_left, affinePoint_eq_frame]

theorem iteratedFDeriv_phase_affine_positive (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (n : ℕ) (x : PhysicalSpace) :
    iteratedFDeriv ℝ (n + 1) (phase (affineCoefficientMap k c B F)) x =
      (iteratedFDeriv ℝ (n + 1) (phase F) (affinePoint c B x)).compContinuousLinearMap
        (fun _ => frameLinearMap B) := by
  have heq : phase (affineCoefficientMap k c B F) =
      fun y => phase F (affinePoint c B y) + (-phase F c) := by
    funext y
    rw [phase_affineCoefficientMap, sub_eq_add_neg]
  rw [heq, iteratedFDeriv_add_apply' (i := n + 1)
    (contDiff_phase_affine_raw k c B F ((n + 1 : ℕ) : WithTop ℕ∞)).contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]
  exact iteratedFDeriv_phase_affine_raw k c B F (n + 1) x

theorem iteratedFDeriv_phase_affine_zero_positive (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k)
    (n : ℕ) (v : Fin (n + 1) → PhysicalSpace) :
    iteratedFDeriv ℝ (n + 1) (phase (affineCoefficientMap k c B F)) 0 v =
      iteratedFDeriv ℝ (n + 1) (phase F) c (fun j => B *ᵥ v j) := by
  rw [iteratedFDeriv_phase_affine_positive, affinePoint_zero]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, frameLinearMap_apply]

end PaperI
