import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open Matrix Filter
open scoped Topology

namespace PaperI.AffineSurfaceDerivatives

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ

def basis (j : Fin 2) : Plane := Pi.single j 1

noncomputable def matrixCLM (B : Matrix (Fin 3) (Fin 3) ℝ) : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi (fun i => ∑ j : Fin 3, B i j • ContinuousLinearMap.proj j)

theorem matrixCLM_apply (B : Matrix (Fin 3) (Fin 3) ℝ) (x : Space) :
    matrixCLM B x = B.mulVec x := by
  ext i
  simp [matrixCLM, Matrix.mulVec, dotProduct]

def affine (B : Matrix (Fin 3) (Fin 3) ℝ) (b : Space) (σ : Plane → Space) : Plane → Space :=
  fun x => b + B.mulVec (σ x)

noncomputable def tangent (σ : Plane → Space) (j : Fin 2) (x : Plane) : Space :=
  fderiv ℝ σ x (basis j)

noncomputable def secondDerivative (σ : Plane → Space) (x : Plane) : Fin 2 → Fin 2 → Space :=
  fun i j => fderiv ℝ (tangent σ j) x (basis i)

theorem affine_hasFDerivAt (B : Matrix (Fin 3) (Fin 3) ℝ) (b : Space)
    (σ : Plane → Space) (x : Plane) (hσ : DifferentiableAt ℝ σ x) :
    HasFDerivAt (affine B b σ) ((matrixCLM B).comp (fderiv ℝ σ x)) x := by
  simpa only [affine, matrixCLM_apply] using
    (((matrixCLM B).hasFDerivAt.comp x hσ.hasFDerivAt).const_add b)

theorem affine_tangent (B : Matrix (Fin 3) (Fin 3) ℝ) (b : Space)
    (σ : Plane → Space) (x : Plane) (hσ : DifferentiableAt ℝ σ x) (j : Fin 2) :
    tangent (affine B b σ) j x = B.mulVec (tangent σ j x) := by
  simp only [tangent, (affine_hasFDerivAt B b σ x hσ).fderiv,
    ContinuousLinearMap.comp_apply, matrixCLM_apply]

theorem affine_secondDerivative (B : Matrix (Fin 3) (Fin 3) ℝ) (b : Space)
    (σ : Plane → Space) (x : Plane)
    (hσ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ σ y)
    (h2 : ∀ j : Fin 2, DifferentiableAt ℝ (tangent σ j) x) (i j : Fin 2) :
    secondDerivative (affine B b σ) x i j = B.mulVec (secondDerivative σ x i j) := by
  have he : tangent (affine B b σ) j =ᶠ[𝓝 x]
      (fun y => matrixCLM B (tangent σ j y)) := by
    filter_upwards [hσ] with y hy
    rw [affine_tangent B b σ y hy, matrixCLM_apply]
  have hd := (matrixCLM B).hasFDerivAt.comp x (h2 j).hasFDerivAt
  simp only [secondDerivative, (hd.congr_of_eventuallyEq he).fderiv,
    ContinuousLinearMap.comp_apply, matrixCLM_apply]

theorem regularity_on (σ : Plane → Space) (U : Set Plane) (hU : IsOpen U)
    (hσ : ContDiffOn ℝ 2 σ U) (x : Plane) (hx : x ∈ U) :
    (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ σ y) ∧
      ∀ j : Fin 2, DifferentiableAt ℝ (tangent σ j) x := by
  constructor
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hσ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  · intro j
    have hd : ContDiffOn ℝ 1 (fderiv ℝ σ) U := hσ.fderiv_of_isOpen hU (by norm_num)
    have hj : ContDiffOn ℝ 1 (tangent σ j) U := hd.clm_apply contDiffOn_const
    exact (hj.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)

theorem affine_contDiffOn (B : Matrix (Fin 3) (Fin 3) ℝ) (b : Space)
    (σ : Plane → Space) (U : Set Plane) (hσ : ContDiffOn ℝ 2 σ U) :
    ContDiffOn ℝ 2 (affine B b σ) U := by
  simpa only [affine, matrixCLM_apply] using
    (contDiffOn_const.add ((matrixCLM B).contDiff.comp_contDiffOn hσ))

end PaperI.AffineSurfaceDerivatives
