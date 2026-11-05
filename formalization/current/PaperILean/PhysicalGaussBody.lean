import PaperILean.PhysicalGaussPivot
import PaperILean.OriginalGaussBodyMatrix

/-! I3353[157,269) in the corrected v18 manuscript (old [143,255)):
actual fixed-physical-center coordinate/body columns and their determinant.
No coefficient-slice substitution or incidence measure identity is asserted. -/

noncomputable section
namespace PaperI.PhysicalGaussBody
open NormalFibers

/-- The existing six affine coordinates, in source order (a,b,c0,d,e,f). -/
noncomputable def fullFrame (w : FrameSpace) (e f : ℝ) : Fin 6 → ℝ :=
  ![w 1, w 2, w 0, w 3, e, f]

/-- The actual fixed-center velocity in coordinates (a,b,c0,d). -/
noncomputable def coordinateVelocity (v : FrameSpace) : Fin 6 → ℝ :=
  ![v 0, v 1, v 2, v 3, 0, 0]

/-- Its body coordinates; the fourth coordinate direction is D-aC. -/
noncomputable def coordinateBody (w v : FrameSpace) : Fin 6 → ℝ :=
  ![v 0, v 1 - w 1 * v 3, v 2, v 3, 0, 0]

theorem framePoint_eq_fullFrame (w : FrameSpace) (e f : ℝ) (x : Fin 3 → ℝ) :
    framePoint w e f x = originalUpperAffineEval (fullFrame w e f) x := by
  ext i
  fin_cases i <;> simp [framePoint, fullFrame, originalUpperAffineEval]

/-- This is the actual h^{-1}h' identity, using the saved homogeneous matrix. -/
theorem actual_coordinate_body_matrix (w v : FrameSpace) (e f : ℝ) :
    (originalAffineHomogeneousMatrix (fullFrame w e f))⁻¹ *
        originalAffineHomogeneousVelocity (coordinateVelocity v) =
      originalAffineHomogeneousVelocity (coordinateBody w v) := by
  have hb : originalAffineBodyCoordinates (fullFrame w e f) (coordinateVelocity v) =
      coordinateBody w v := by
    ext i
    fin_cases i <;> simp [originalAffineBodyCoordinates, fullFrame,
      coordinateVelocity, coordinateBody]
  rw [originalAffineHomogeneousMatrix_body, hb]

def coordinateLinear : FrameSpace →L[ℝ] FrameSpace :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 3]

/-- The preceding velocity really differentiates the physical coordinate curve. -/
theorem coordinate_curve_hasDerivAt (w v : FrameSpace) (e f : ℝ) :
    HasDerivAt (fun t : ℝ => fullFrame (w + t • coordinateLinear v) e f)
      (coordinateVelocity v) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [fullFrame, coordinateVelocity, coordinateLinear] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (w 1)
  · simpa [fullFrame, coordinateVelocity, coordinateLinear] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (w 2)
  · simpa [fullFrame, coordinateVelocity, coordinateLinear] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (w 0)
  · simpa [fullFrame, coordinateVelocity, coordinateLinear] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v 3)).const_add (w 3)
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

/-- Pure body parameters are (A,C,Tx,D); D also changes the physical b-coordinate. -/
def bodyLinear (a : ℝ) : FrameSpace →L[ℝ] FrameSpace :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 1 + a • ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 3]

def bodyFrame (w u : FrameSpace) : FrameSpace := w + bodyLinear (w 1) u

/-- The increment is literal right composition of actual affine maps. -/
theorem bodyFrame_right_composition (w u : FrameSpace) (e f : ℝ) (x : Fin 3 → ℝ) :
    framePoint (bodyFrame w u) e f x =
      framePoint w e f (framePoint (coordinateLinear u) 0 0 x) := by
  ext i
  fin_cases i <;> simp [framePoint, bodyFrame, bodyLinear, coordinateLinear] <;> ring

/-- Full polynomial evaluation intertwines that same actual right composition. -/
theorem full_polynomial_body_pullback (G : Poly) (w u : FrameSpace) (e f : ℝ)
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (pullback (bodyFrame w u) e f G) =
      MvPolynomial.eval (framePoint (coordinateLinear u) 0 0 x) (pullback w e f G) := by
  rw [eval_pullback, eval_pullback, bodyFrame_right_composition]

/-- Actual normalization equations along the pure-body affine increment. -/
def bodyNormalization (G : Poly) (e f : ℝ) (w u : FrameSpace) : FrameSpace :=
  normalizationEquationsI G e f (bodyFrame w u)

private theorem hasFDerivAt_bodyFrame (w : FrameSpace) :
    HasFDerivAt (bodyFrame w) (bodyLinear (w 1)) 0 := by
  simpa [bodyFrame] using (bodyLinear (w 1)).hasFDerivAt.const_add w

/-- No differential is an assumption: differentiate the actual composition. -/
theorem bodyNormalization_fderiv (G : Poly) (e f : ℝ) (w : FrameSpace) :
    fderiv ℝ (bodyNormalization G e f w) 0 =
      (fderiv ℝ (normalizationEquationsI G e f) w).comp (bodyLinear (w 1)) := by
  have hN := hasFDerivAt_normalizationEquationsI G e f w
  have hN' : HasFDerivAt (normalizationEquationsI G e f)
      (normalizationDifferentialI G e f w) (bodyFrame w 0) := by
    simpa [bodyFrame] using hN
  have h := HasFDerivAt.comp (g := normalizationEquationsI G e f)
    (f := bodyFrame w) (0 : FrameSpace) hN' (hasFDerivAt_bodyFrame w)
  simpa [bodyNormalization, hN.fderiv] using h.fderiv

/-- Matrix of the body-to-coordinate map, including the even cyclic reorder. -/
noncomputable def bodyChangeMatrix (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,1,0; 1,0,0,0; 0,1,0,a; 0,0,0,1]

private theorem bodyLinear_single (a : ℝ) (j : Fin 4) :
    bodyLinear a (Pi.single j 1) =
      ∑ k : Fin 4, (bodyChangeMatrix a k j) • (Pi.single k 1 : FrameSpace) := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [bodyLinear, bodyChangeMatrix, Fin.sum_univ_succ, Pi.single_apply]

/-- Exact equality for the actual normalization derivative, not an arbitrary matrix. -/
theorem bodyNormalization_jacobian (G : Poly) (e f : ℝ) (w : FrameSpace) :
    ordinaryJacobian (bodyNormalization G e f w) 0 =
      ordinaryJacobian (normalizationEquationsI G e f) w * bodyChangeMatrix (w 1) := by
  ext i j
  rw [ordinaryJacobian, bodyNormalization_fderiv, ContinuousLinearMap.comp_apply,
    bodyLinear_single, map_sum]
  simp [Matrix.mul_apply, ordinaryJacobian, map_smul, Finset.sum_apply, mul_comm]

theorem det_bodyChangeMatrix (a : ℝ) : (bodyChangeMatrix a).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [bodyChangeMatrix, Fin.sum_univ_succ, Matrix.det_fin_three] <;> rfl

/-- I3353's complete body-column conversion, specialized to the full derivative F_x.
The arbitrary frame and physical center are retained; no pivot, normalization,
differential identity or determinant conclusion is assumed. -/
theorem physical_gauss_body_stage (F : Poly) (e f : ℝ) (w : FrameSpace) :
    (∀ v : FrameSpace,
      (originalAffineHomogeneousMatrix (fullFrame w e f))⁻¹ *
          originalAffineHomogeneousVelocity (coordinateVelocity v) =
        originalAffineHomogeneousVelocity (coordinateBody w v)) ∧
    (∀ u : FrameSpace, ∀ x : Fin 3 → ℝ,
      MvPolynomial.eval x (pullback (bodyFrame w u) e f (MvPolynomial.pderiv 0 F)) =
        MvPolynomial.eval (framePoint (coordinateLinear u) 0 0 x)
          (pullback w e f (MvPolynomial.pderiv 0 F))) ∧
    (ordinaryJacobian (bodyNormalization (MvPolynomial.pderiv 0 F) e f w) 0).det =
      (ordinaryJacobian (normalizationEquationsI (MvPolynomial.pderiv 0 F) e f) w).det ∧
    |(ordinaryJacobian (bodyNormalization (MvPolynomial.pderiv 0 F) e f w) 0).det| =
      |(ordinaryJacobian (normalizationEquationsI (MvPolynomial.pderiv 0 F) e f) w).det| := by
  refine ⟨fun v => actual_coordinate_body_matrix w v e f,
    fun u x => full_polynomial_body_pullback _ w u e f x, ?_, ?_⟩
  · rw [bodyNormalization_jacobian, Matrix.det_mul, det_bodyChangeMatrix, mul_one]
  · rw [bodyNormalization_jacobian, Matrix.det_mul, det_bodyChangeMatrix, mul_one]

end PaperI.PhysicalGaussBody
