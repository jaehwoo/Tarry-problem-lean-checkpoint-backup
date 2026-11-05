import PaperILean.OriginalGaussRelativeFrameIntegration
import Mathlib.Analysis.Matrix

/-! I1533[62,203)+I1534-I1540: the actual moving d-chart gauge.
The right change is G S⁻¹, and its body derivative includes the genuine
- S' S⁻¹ term. No quantitative comparison or necessity assertion is made. -/

noncomputable section
namespace PaperI.OriginalDGauge

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedSpace

/-- The source affine change S(x,y,z)=(x-beta*y,y,z+eta). -/
def gaugeFrame (beta eta : ℝ) : Fin 6 → ℝ := ![-beta,0,0,0,0,eta]

/-- Right multiplication by the actual inverse source change. -/
def gaugePoint (g : Fin 6 → ℝ) (beta eta : ℝ) : Fin 6 → ℝ :=
  originalUpperAffineComp g (originalUpperAffineInv (gaugeFrame beta eta))

def gaugedPath (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ) (t : ℝ) : Fin 6 → ℝ :=
  gaugePoint (g t) (beta t) (eta t)

theorem gaugeFrame_eval (beta eta : ℝ) (x : Fin 3 → ℝ) :
    originalUpperAffineEval (gaugeFrame beta eta) x =
      ![x 0-beta*x 1,x 1,x 2+eta] := by
  ext i
  fin_cases i <;> simp [gaugeFrame, originalUpperAffineEval]
  ring

theorem gaugePoint_coordinates (g : Fin 6 → ℝ) (beta eta : ℝ) :
    gaugePoint g beta eta =
      ![g 0+beta,g 1,g 2-g 1*eta,g 3,g 4-g 3*eta,g 5-eta] := by
  ext i
  fin_cases i <;>
    simp [gaugePoint,gaugeFrame,originalUpperAffineComp,originalUpperAffineInv] <;> ring

theorem gaugePoint_matrix (g : Fin 6 → ℝ) (beta eta : ℝ) :
    originalAffineHomogeneousMatrix (gaugePoint g beta eta) =
      originalAffineHomogeneousMatrix g * (originalAffineHomogeneousMatrix (gaugeFrame beta eta))⁻¹ := by
  rw [gaugePoint, originalAffineHomogeneousMatrix_comp, originalAffineHomogeneousMatrix_inverse]

theorem gaugedPath_matrix (g : ℝ → Fin 6 → ℝ) (beta eta : ℝ → ℝ) (t : ℝ) :
    originalAffineHomogeneousMatrix (gaugedPath g beta eta t) =
      originalAffineHomogeneousMatrix (g t) *
        (originalAffineHomogeneousMatrix (gaugeFrame (beta t) (eta t)))⁻¹ :=
  gaugePoint_matrix _ _ _

/-- Exact six body coefficients after the source two non-simple rates are removed. -/
def gaugeBodyRates (b : Fin 6 → ℝ) (dbeta deta : ℝ) : Fin 6 → ℝ :=
  ![b 0+dbeta,0,b 2-b 1*b 4,1,0,b 5-deta]

private def gaugeVelocity (g v : Fin 6 → ℝ) (eta dbeta deta : ℝ) : Fin 6 → ℝ :=
  ![v 0+dbeta,v 1,v 2-(v 1*eta+g 1*deta),v 3,
    v 4-(v 3*eta+g 3*deta),v 5-deta]

private theorem gaugedPath_raw_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t dbeta deta : ℝ) (hg : HasDerivAt g v t)
    (hb : HasDerivAt beta dbeta t) (he : HasDerivAt eta deta t) :
    HasDerivAt (gaugedPath g beta eta) (gaugeVelocity (g t) v (eta t) dbeta deta) t := by
  have h := hasDerivAt_pi.mp hg
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using (h 0).add hb
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 1
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using (h 2).sub ((h 1).mul he)
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 3
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using (h 4).sub ((h 3).mul he)
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using (h 5).sub he

/-- Genuine derivative of the actual gauged path in its own body coordinates. -/
theorem gaugedPath_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (b : Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t dbeta deta : ℝ)
    (hg : HasDerivAt g (originalUpperBodyVelocity (g t) b) t)
    (hb : HasDerivAt beta dbeta t) (he : HasDerivAt eta deta t)
    (hbeta : beta t = b 1) (heta : eta t = b 4) (hD : b 3 = 1) :
    HasDerivAt (gaugedPath g beta eta)
      (originalUpperBodyVelocity (gaugedPath g beta eta t) (gaugeBodyRates b dbeta deta)) t := by
  convert gaugedPath_raw_hasDerivAt g (originalUpperBodyVelocity (g t) b)
    beta eta t dbeta deta hg hb he using 1
  ext i
  fin_cases i <;>
    simp [gaugedPath,gaugePoint_coordinates,gaugeVelocity,originalUpperBodyVelocity,
      gaugeBodyRates,hbeta,heta,hD] <;> ring

private theorem gaugeFrame_hasDerivAt (beta eta : ℝ → ℝ) (t dbeta deta : ℝ)
    (hb : HasDerivAt beta dbeta t) (he : HasDerivAt eta deta t) :
    HasDerivAt (fun u => gaugeFrame (beta u) (eta u)) ![-dbeta,0,0,0,0,deta] t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [gaugeFrame] using hb.neg
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const t 0
  · simpa [gaugeFrame] using he

/-- Literal matrix conjugation and derivative correction in the source convention. -/
theorem gauge_matrix_generator (b : Fin 6 → ℝ) (dbeta deta : ℝ) (hD : b 3 = 1) :
    originalAffineHomogeneousMatrix (gaugeFrame (b 1) (b 4)) *
        originalAffineHomogeneousVelocity b *
        (originalAffineHomogeneousMatrix (gaugeFrame (b 1) (b 4)))⁻¹ -
      originalAffineHomogeneousVelocity ![-dbeta,0,0,0,0,deta] *
        (originalAffineHomogeneousMatrix (gaugeFrame (b 1) (b 4)))⁻¹ =
      originalAffineHomogeneousVelocity (gaugeBodyRates b dbeta deta) := by
  rw [originalAffineHomogeneousMatrix_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalAffineHomogeneousMatrix,originalAffineHomogeneousVelocity,
      gaugeFrame,originalUpperAffineInv,gaugeBodyRates,Matrix.mul_apply,
      Fin.sum_univ_succ,hD]
  ring

/-- The complete actual moving-gauge identity of I1533[62,203)+I1534-I1540.
The original C,Ty rates and D parameter are identified from the genuine path derivative.
The source mixed rate is exactly xi-beta*eta; no extra pivot or estimate is assumed. -/
theorem actual_d_gauge_stage
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (beta eta : ℝ → ℝ)
    (t dbeta deta : ℝ) (hg : HasDerivAt g v t)
    (hb : HasDerivAt beta dbeta t) (he : HasDerivAt eta deta t)
    (hbeta : beta t = originalAffineBodyCoordinates (g t) v 1)
    (heta : eta t = originalAffineBodyCoordinates (g t) v 4)
    (hD : originalAffineBodyCoordinates (g t) v 3 = 1) :
    (∀ u, originalAffineHomogeneousMatrix (gaugedPath g beta eta u) =
      originalAffineHomogeneousMatrix (g u) *
        (originalAffineHomogeneousMatrix (gaugeFrame (beta u) (eta u)))⁻¹) ∧
      HasDerivAt (gaugedPath g beta eta)
        (originalUpperBodyVelocity (gaugedPath g beta eta t)
          (gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dbeta deta)) t ∧
      originalAffineBodyCoordinates (gaugedPath g beta eta t)
        (deriv (gaugedPath g beta eta) t) =
          gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dbeta deta ∧
      (originalAffineHomogeneousMatrix (gaugedPath g beta eta t))⁻¹ *
          deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g beta eta u)) t =
        originalAffineHomogeneousMatrix (gaugeFrame (beta t) (eta t)) *
            originalAffineHomogeneousVelocity (originalAffineBodyCoordinates (g t) v) *
            (originalAffineHomogeneousMatrix (gaugeFrame (beta t) (eta t)))⁻¹ -
          deriv (fun u => originalAffineHomogeneousMatrix (gaugeFrame (beta u) (eta u))) t *
            (originalAffineHomogeneousMatrix (gaugeFrame (beta t) (eta t)))⁻¹ ∧
      (originalAffineHomogeneousMatrix (gaugedPath g beta eta t))⁻¹ *
          deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g beta eta u)) t =
        originalAffineHomogeneousVelocity
          (gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dbeta deta) := by
  let b := originalAffineBodyCoordinates (g t) v
  have hg' : HasDerivAt g (originalUpperBodyVelocity (g t) b) t := by
    simpa only [b,originalUpperBodyVelocity_body] using hg
  have hq := gaugedPath_hasDerivAt g b beta eta t dbeta deta hg' hb he hbeta heta hD
  have hbody : originalAffineBodyCoordinates (gaugedPath g beta eta t)
      (deriv (gaugedPath g beta eta) t) = gaugeBodyRates b dbeta deta := by
    rw [hq.deriv,originalUpperBodyCoordinates_velocity]
  have hmatrix := originalAffineHomogeneousMatrix_hasDerivAt _ _ t hq
  have hactual : (originalAffineHomogeneousMatrix (gaugedPath g beta eta t))⁻¹ *
      deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g beta eta u)) t =
        originalAffineHomogeneousVelocity (gaugeBodyRates b dbeta deta) := by
    rw [hmatrix.deriv,originalAffineHomogeneousMatrix_body,originalUpperBodyCoordinates_velocity]
  have hs := originalAffineHomogeneousMatrix_hasDerivAt _ _ t
    (gaugeFrame_hasDerivAt beta eta t dbeta deta hb he)
  refine ⟨gaugedPath_matrix g beta eta,hq,hbody,?_,hactual⟩
  rw [hactual,hs.deriv,hbeta,heta]
  exact (gauge_matrix_generator b dbeta deta hD).symm

end PaperI.OriginalDGauge
