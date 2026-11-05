import PaperILean.OriginalDGauge

/-! I1543-I1549: exact multiplication from the anchored moving d-chart
frame back to the original coordinates. The two anchors are the actual
values of one original path and one moving frame. No size or regularity
assumption is needed for this pointwise group identity. -/

noncomputable section
namespace PaperI.OriginalDGaugeMultiplyback
open OriginalDGauge

/-- The six displayed original relative coordinates, in (a,b,c,d,e,f) order. -/
def multiplyback (q : Fin 6 → ℝ) (beta0 beta eta0 eta : ℝ) : Fin 6 → ℝ :=
  ![q 0 + beta0 - beta,
    q 1 + beta0 * q 3,
    q 2 + beta0 * q 4 + (q 1 + beta0 * q 3) * eta,
    q 3,
    q 4 + q 3 * eta,
    q 5 + eta - eta0]

theorem multiplyback_eq_comp (q : Fin 6 → ℝ) (beta0 beta eta0 eta : ℝ) :
    multiplyback q beta0 beta eta0 eta =
      originalUpperAffineComp
        (originalUpperAffineComp (originalUpperAffineInv (gaugeFrame beta0 eta0)) q)
        (gaugeFrame beta eta) := by
  ext i
  fin_cases i <;>
    simp [multiplyback, gaugeFrame, originalUpperAffineComp, originalUpperAffineInv] <;> ring

theorem gauged_relative_multiplyback (g0 g : Fin 6 → ℝ)
    (beta0 beta eta0 eta : ℝ) :
    multiplyback
      (originalUpperRelativeFrame (gaugePoint g0 beta0 eta0) (gaugePoint g beta eta))
      beta0 beta eta0 eta = originalUpperRelativeFrame g0 g := by
  ext i
  fin_cases i <;>
    simp [multiplyback, gaugePoint, gaugeFrame, originalUpperRelativeFrame,
      originalUpperAffineComp, originalUpperAffineInv] <;> ring

theorem multiplyback_matrix (q : Fin 6 → ℝ) (beta0 beta eta0 eta : ℝ) :
    originalAffineHomogeneousMatrix (multiplyback q beta0 beta eta0 eta) =
      (originalAffineHomogeneousMatrix (gaugeFrame beta0 eta0))⁻¹ *
        originalAffineHomogeneousMatrix q *
        originalAffineHomogeneousMatrix (gaugeFrame beta eta) := by
  rw [multiplyback_eq_comp, originalAffineHomogeneousMatrix_comp,
    originalAffineHomogeneousMatrix_comp, ← originalAffineHomogeneousMatrix_inverse]

theorem gauged_relative_matrix_multiplyback (g0 g : Fin 6 → ℝ)
    (beta0 beta eta0 eta : ℝ) :
    (originalAffineHomogeneousMatrix g0)⁻¹ * originalAffineHomogeneousMatrix g =
      (originalAffineHomogeneousMatrix (gaugeFrame beta0 eta0))⁻¹ *
        ((originalAffineHomogeneousMatrix (gaugePoint g0 beta0 eta0))⁻¹ *
          originalAffineHomogeneousMatrix (gaugePoint g beta eta)) *
        originalAffineHomogeneousMatrix (gaugeFrame beta eta) := by
  calc
    _ = originalAffineHomogeneousMatrix (originalUpperRelativeFrame g0 g) :=
      originalAffineHomogeneousMatrix_relative g0 g
    _ = originalAffineHomogeneousMatrix
        (multiplyback
          (originalUpperRelativeFrame (gaugePoint g0 beta0 eta0) (gaugePoint g beta eta))
          beta0 beta eta0 eta) :=
      congrArg originalAffineHomogeneousMatrix
        (gauged_relative_multiplyback g0 g beta0 beta eta0 eta).symm
    _ = (originalAffineHomogeneousMatrix (gaugeFrame beta0 eta0))⁻¹ *
        originalAffineHomogeneousMatrix
          (originalUpperRelativeFrame (gaugePoint g0 beta0 eta0) (gaugePoint g beta eta)) *
        originalAffineHomogeneousMatrix (gaugeFrame beta eta) :=
      multiplyback_matrix _ beta0 beta eta0 eta
    _ = _ := by rw [← originalAffineHomogeneousMatrix_relative]

/-- A path in the changed frame, measured from its actual changed-frame anchor. -/
def gaugedRelativePath (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 t : ℝ) : Fin 6 → ℝ :=
  originalUpperRelativeFrame (gaugedPath g beta eta t0) (gaugedPath g beta eta t)

theorem gaugedRelativePath_anchor (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t0 : ℝ) : gaugedRelativePath g beta eta t0 t0 = 0 := by
  exact originalUpperRelativeFrame_self _

/-- The complete six-coordinate multiplyback stage of I1543-I1549.
The homogeneous identity records its multiplication order and both actual
anchors; the final conjunct fixes the identity at the changed-frame anchor. -/
theorem actual_d_gauge_multiplyback_stage (g : ℝ → Fin 6 → ℝ)
    (beta eta : ℝ → ℝ) (t0 t : ℝ) :
    let q := gaugedRelativePath g beta eta t0 t
    originalUpperRelativeFrame (g t0) (g t) =
      ![q 0 + beta t0 - beta t,
        q 1 + beta t0 * q 3,
        q 2 + beta t0 * q 4 + (q 1 + beta t0 * q 3) * eta t,
        q 3,
        q 4 + q 3 * eta t,
        q 5 + eta t - eta t0] ∧
    (originalAffineHomogeneousMatrix (g t0))⁻¹ * originalAffineHomogeneousMatrix (g t) =
      (originalAffineHomogeneousMatrix (gaugeFrame (beta t0) (eta t0)))⁻¹ *
        ((originalAffineHomogeneousMatrix (gaugedPath g beta eta t0))⁻¹ *
          originalAffineHomogeneousMatrix (gaugedPath g beta eta t)) *
        originalAffineHomogeneousMatrix (gaugeFrame (beta t) (eta t)) ∧
    gaugedRelativePath g beta eta t0 t0 = 0 := by
  refine ⟨?_, ?_, gaugedRelativePath_anchor g beta eta t0⟩
  · exact (gauged_relative_multiplyback (g t0) (g t)
      (beta t0) (beta t) (eta t0) (eta t)).symm
  · exact gauged_relative_matrix_multiplyback (g t0) (g t)
      (beta t0) (beta t) (eta t0) (eta t)

end PaperI.OriginalDGaugeMultiplyback
