import PaperILean.OriginalHaarOrbitBody
import PaperILean.AugmentedOrbit
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual augmented path differentiation for I3239[170,378), I3240-I3242.
All physical affine coefficients, including their constants, are retained.
The D body component is derived from the local section-coordinate identity. -/

noncomputable section
namespace PaperI.RegularSectionDifferential

open Filter Matrix
open scoped Topology

-- These local instances supply the usual finite-coordinate topology for differentiation.
-- No equality with the manuscript's separately defined Euclidean norm is asserted.
noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- Composition of the full physical affine map with the original upper-affine map. -/
noncomputable def physicalPullback (ell : PhysicalAffineData) (g : Fin 6 → ℝ) :
    PhysicalAffineData :=
  (ell.1 + ell.2 *ᵥ ![g 2, g 4, g 5], ell.2 * originalUpperLinearMatrix g)

/-- The actual augmented coefficient action; physical entries remain parameters. -/
noncomputable def augmentedPullback {k : ℕ} (S0 : AugmentedState k)
    (g : Fin 6 → ℝ) : AugmentedState k :=
  (originalUpperCoefficientPullback S0.1 g, physicalPullback S0.2 g)

private noncomputable def physicalRate (ell : PhysicalAffineData) :
    (Fin 6 → ℝ) →ₗ[ℝ] PhysicalAffineData where
  toFun v := physicalAffineFieldAction ell (upperAffineFieldTranslation v)
    (upperAffineFieldLinear v)
  map_add' v w := by
    simp only [upperAffineFieldTranslation_add, upperAffineFieldLinear_add,
      physicalAffineFieldAction_add]
  map_smul' r v := by
    simp only [upperAffineFieldTranslation_smul, upperAffineFieldLinear_smul,
      physicalAffineFieldAction_smul, RingHom.id_apply]

private theorem upperMatrix_eq_one_add_field (g : Fin 6 → ℝ) :
    originalUpperLinearMatrix g = 1 + upperAffineFieldLinear g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalUpperLinearMatrix, upperAffineFieldLinear, Matrix.one_apply]

private theorem physicalPullback_eq (ell : PhysicalAffineData) (g : Fin 6 → ℝ) :
    physicalPullback ell g = ell + physicalRate ell g := by
  apply Prod.ext
  · rfl
  · change ell.2 * originalUpperLinearMatrix g = ell.2 + ell.2 * upperAffineFieldLinear g
    rw [upperMatrix_eq_one_add_field, mul_add, mul_one]

private theorem physicalPullback_hasDerivAt (ell : PhysicalAffineData)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => physicalPullback ell (g u)) (physicalRate ell v) t := by
  have h := (hasDerivAt_const t ell).add
    ((LinearMap.toContinuousLinearMap (physicalRate ell)).hasFDerivAt.comp_hasDerivAt t hg)
  simpa only [physicalPullback_eq, Function.comp_def, zero_add,
    LinearMap.coe_toContinuousLinearMap'] using h

private theorem upperMatrix_body_translation (g v : Fin 6 → ℝ) :
    originalUpperLinearMatrix g *ᵥ
        upperAffineFieldTranslation (originalAffineBodyCoordinates g v) =
      upperAffineFieldTranslation v := by
  ext i
  fin_cases i <;>
    simp [originalUpperLinearMatrix, upperAffineFieldTranslation,
      originalAffineBodyCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem upperMatrix_body_linear (g v : Fin 6 → ℝ) :
    originalUpperLinearMatrix g * upperAffineFieldLinear (originalAffineBodyCoordinates g v) =
      upperAffineFieldLinear v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalUpperLinearMatrix, upperAffineFieldLinear,
      originalAffineBodyCoordinates, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Physical derivative expressed at the current augmented state in body coordinates.
The initial physical matrix may be singular. -/
theorem physicalRate_eq_body (ell : PhysicalAffineData) (g v : Fin 6 → ℝ) :
    physicalAffineFieldAction ell (upperAffineFieldTranslation v) (upperAffineFieldLinear v) =
      physicalAffineFieldAction (physicalPullback ell g)
        (upperAffineFieldTranslation (originalAffineBodyCoordinates g v))
        (upperAffineFieldLinear (originalAffineBodyCoordinates g v)) := by
  apply Prod.ext
  · change ell.2 *ᵥ upperAffineFieldTranslation v =
      (ell.2 * originalUpperLinearMatrix g) *ᵥ
        upperAffineFieldTranslation (originalAffineBodyCoordinates g v)
    rw [← Matrix.mulVec_mulVec, upperMatrix_body_translation]
  · change ell.2 * upperAffineFieldLinear v =
      (ell.2 * originalUpperLinearMatrix g) *
        upperAffineFieldLinear (originalAffineBodyCoordinates g v)
    rw [Matrix.mul_assoc, upperMatrix_body_linear]

/-- Chain rule for the actual augmented path, without assuming its orbit equation. -/
theorem augmentedPullback_hasDerivAt_body {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => augmentedPullback S0 (g u))
      (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (originalAffineBodyCoordinates (g t) v)) t := by
  have hphase := OriginalHaarOrbitBody.orbit_hasDerivAt_body S0.1 g v t hg
  have hphysical := physicalPullback_hasDerivAt S0.2 g v t hg
  have hbody := physicalRate_eq_body S0.2 (g t) v
  change physicalRate S0.2 v = _ at hbody
  rw [hbody] at hphysical
  exact hphase.prodMk hphysical

/-- The actual coordinate-path derivative is the original six-column augmented matrix. -/
theorem coordinates_hasDerivAt_body {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)))
      (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
        originalAffineBodyCoordinates (g t) v) t := by
  have h := (LinearMap.toContinuousLinearMap
      (augmentedStateCoordinates k).toLinearMap).hasFDerivAt.comp_hasDerivAt t
    (augmentedPullback_hasDerivAt_body S0 g v t hg)
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap',
    LinearEquiv.coe_toLinearMap, augmentedOrbitMatrix_mulVec] using h

/-- The local equation d(g(u))=u forces the actual D body coefficient to be one. -/
theorem section_body_D_eq_one (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (t : ℝ) (hg : HasDerivAt g v t)
    (hd : ∀ᶠ u in 𝓝 t, g u 3 = u) : originalAffineBodyCoordinates (g t) v 3 = 1 := by
  have hcoord : HasDerivAt (fun u => g u 3) (v 3) t := (hasDerivAt_pi.mp hg) 3
  have hone : HasDerivAt (fun u => g u 3) 1 t :=
    (hasDerivAt_id t).congr_of_eventuallyEq hd
  simpa only [originalAffineBodyCoordinates, Matrix.cons_val_succ, Matrix.cons_val_zero]
    using hcoord.unique hone

end PaperI.RegularSectionDifferential
