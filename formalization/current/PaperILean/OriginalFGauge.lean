import PaperILean.OriginalGaussRelativeFrameIntegration
import Mathlib.Analysis.Matrix

/-! I1563-I1566 and I1567[202,219)+I1568-I1570: the actual terminal-chart
moving gauge and its coordinate equations. Here tau is the original Tx rate,
not the mixed rate of the preceding d chart. Corrected delta is kept explicit.
No smallness, nondegeneracy, covering or model-comparison assertion is made. -/

noncomputable section
namespace PaperI.OriginalFGauge

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.normedSpace

/-- The actual source change S(x,y,z)=(x-tau*z,y-eta*z,z). -/
def gaugeFrame (tau eta : ℝ) : Fin 6 → ℝ := ![0,-tau,0,-eta,0,0]

def gaugePoint (g : Fin 6 → ℝ) (tau eta : ℝ) : Fin 6 → ℝ :=
  originalUpperAffineComp g (originalUpperAffineInv (gaugeFrame tau eta))

def gaugedPath (g : ℝ → Fin 6 → ℝ) (tau eta : ℝ → ℝ) (t : ℝ) : Fin 6 → ℝ :=
  gaugePoint (g t) (tau t) (eta t)

theorem gaugeFrame_eval (tau eta : ℝ) (x : Fin 3 → ℝ) :
    originalUpperAffineEval (gaugeFrame tau eta) x =
      ![x 0-tau*x 2,x 1-eta*x 2,x 2] := by
  ext i
  fin_cases i <;> simp [gaugeFrame,originalUpperAffineEval] <;> ring

theorem gaugeFrame_inverse (tau eta : ℝ) :
    originalUpperAffineInv (gaugeFrame tau eta) = ![0,tau,0,eta,0,0] := by
  ext i
  fin_cases i <;> simp [gaugeFrame,originalUpperAffineInv]

theorem gaugePoint_coordinates (g : Fin 6 → ℝ) (tau eta : ℝ) :
    gaugePoint g tau eta = ![g 0,g 1+tau+g 0*eta,g 2,g 3+eta,g 4,g 5] := by
  ext i
  fin_cases i <;>
    simp [gaugePoint,gaugeFrame_inverse,originalUpperAffineComp] <;> ring

theorem gaugePoint_matrix (g : Fin 6 → ℝ) (tau eta : ℝ) :
    originalAffineHomogeneousMatrix (gaugePoint g tau eta) =
      originalAffineHomogeneousMatrix g * (originalAffineHomogeneousMatrix (gaugeFrame tau eta))⁻¹ := by
  rw [gaugePoint,originalAffineHomogeneousMatrix_comp,originalAffineHomogeneousMatrix_inverse]

theorem gaugedPath_matrix (g : ℝ → Fin 6 → ℝ) (tau eta : ℝ → ℝ) (t : ℝ) :
    originalAffineHomogeneousMatrix (gaugedPath g tau eta t) =
      originalAffineHomogeneousMatrix (g t) *
        (originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)))⁻¹ :=
  gaugePoint_matrix _ _ _

/-- Original body order is A,C,Tx,D,Ty,Tz. The corrected D rate is b3+deta. -/
def gaugeBodyRates (b : Fin 6 → ℝ) (dtau deta : ℝ) : Fin 6 → ℝ :=
  ![b 0,b 1+b 0*b 4+dtau,0,b 3+deta,0,1]

private def gaugeVelocity (g v : Fin 6 → ℝ) (eta dtau deta : ℝ) : Fin 6 → ℝ :=
  ![v 0,v 1+dtau+(v 0*eta+g 0*deta),v 2,v 3+deta,v 4,v 5]

private theorem gaugedPath_raw_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (tau eta : ℝ → ℝ)
    (t dtau deta : ℝ) (hg : HasDerivAt g v t)
    (ht : HasDerivAt tau dtau t) (he : HasDerivAt eta deta t) :
    HasDerivAt (gaugedPath g tau eta) (gaugeVelocity (g t) v (eta t) dtau deta) t := by
  have h := hasDerivAt_pi.mp hg
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 0
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using ((h 1).add ht).add ((h 0).mul he)
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 2
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using (h 3).add he
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 4
  · simpa [gaugedPath,gaugePoint_coordinates,gaugeVelocity] using h 5

theorem gaugedPath_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (b : Fin 6 → ℝ) (tau eta : ℝ → ℝ)
    (t dtau deta : ℝ)
    (hg : HasDerivAt g (originalUpperBodyVelocity (g t) b) t)
    (ht : HasDerivAt tau dtau t) (he : HasDerivAt eta deta t)
    (htau : tau t = b 2) (heta : eta t = b 4) (hF : b 5 = 1) :
    HasDerivAt (gaugedPath g tau eta)
      (originalUpperBodyVelocity (gaugedPath g tau eta t) (gaugeBodyRates b dtau deta)) t := by
  convert gaugedPath_raw_hasDerivAt g (originalUpperBodyVelocity (g t) b)
    tau eta t dtau deta hg ht he using 1
  ext i
  fin_cases i <;>
    simp [gaugedPath,gaugePoint_coordinates,gaugeVelocity,originalUpperBodyVelocity,
      gaugeBodyRates,htau,heta,hF] <;> ring

private theorem gaugeFrame_hasDerivAt (tau eta : ℝ → ℝ) (t dtau deta : ℝ)
    (ht : HasDerivAt tau dtau t) (he : HasDerivAt eta deta t) :
    HasDerivAt (fun u => gaugeFrame (tau u) (eta u)) ![0,-dtau,0,-deta,0,0] t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const t 0
  · simpa [gaugeFrame] using ht.neg
  · exact hasDerivAt_const t 0
  · simpa [gaugeFrame] using he.neg
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_const t 0

/-- The literal conjugation-minus-derivative formula, including both derivative signs. -/
theorem gauge_matrix_generator (b : Fin 6 → ℝ) (dtau deta : ℝ) (hF : b 5 = 1) :
    originalAffineHomogeneousMatrix (gaugeFrame (b 2) (b 4)) *
        originalAffineHomogeneousVelocity b *
        (originalAffineHomogeneousMatrix (gaugeFrame (b 2) (b 4)))⁻¹ -
      originalAffineHomogeneousVelocity ![0,-dtau,0,-deta,0,0] *
        (originalAffineHomogeneousMatrix (gaugeFrame (b 2) (b 4)))⁻¹ =
      originalAffineHomogeneousVelocity (gaugeBodyRates b dtau deta) := by
  rw [originalAffineHomogeneousMatrix_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalAffineHomogeneousMatrix,originalAffineHomogeneousVelocity,
      gaugeFrame,originalUpperAffineInv,gaugeBodyRates,Matrix.mul_apply,
      Fin.sum_univ_succ,hF]
  ring

/-- Actual bounded terminal-chart gauge, its body identity and all six coordinate equations.
The source tau,eta are identified from the genuine ORIGINAL derivative. The manuscript
relabels b3+deta as delta; here that corrected rate remains explicit. -/
theorem actual_f_gauge_stage
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (tau eta : ℝ → ℝ)
    (t dtau deta P C : ℝ) (hP : 2 ≤ P) (hg : HasDerivAt g v t)
    (ht : HasDerivAt tau dtau t) (he : HasDerivAt eta deta t)
    (htau : tau t = originalAffineBodyCoordinates (g t) v 2)
    (heta : eta t = originalAffineBodyCoordinates (g t) v 4)
    (hF : originalAffineBodyCoordinates (g t) v 5 = 1)
    (hbody : ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) v i| ≤ P^C) :
    (∀ u, originalAffineHomogeneousMatrix (gaugedPath g tau eta u) =
      originalAffineHomogeneousMatrix (g u) *
        (originalAffineHomogeneousMatrix (gaugeFrame (tau u) (eta u)))⁻¹) ∧
      HasDerivAt (gaugedPath g tau eta)
        (originalUpperBodyVelocity (gaugedPath g tau eta t)
          (gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dtau deta)) t ∧
      originalAffineBodyCoordinates (gaugedPath g tau eta t)
        (deriv (gaugedPath g tau eta) t) =
          gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dtau deta ∧
      (originalAffineHomogeneousMatrix (gaugedPath g tau eta t))⁻¹ *
          deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g tau eta u)) t =
        originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)) *
            originalAffineHomogeneousVelocity (originalAffineBodyCoordinates (g t) v) *
            (originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)))⁻¹ -
          deriv (fun u => originalAffineHomogeneousMatrix (gaugeFrame (tau u) (eta u))) t *
            (originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)))⁻¹ ∧
      (originalAffineHomogeneousMatrix (gaugedPath g tau eta t))⁻¹ *
          deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g tau eta u)) t =
        originalAffineHomogeneousVelocity
          (gaugeBodyRates (originalAffineBodyCoordinates (g t) v) dtau deta) ∧
      HasDerivAt (gaugedPath g tau eta)
        ![originalAffineBodyCoordinates (g t) v 0,
          gaugedPath g tau eta t 0 * (originalAffineBodyCoordinates (g t) v 3+deta) +
            (originalAffineBodyCoordinates (g t) v 1+
              originalAffineBodyCoordinates (g t) v 0*eta t+dtau),
          gaugedPath g tau eta t 1,originalAffineBodyCoordinates (g t) v 3+deta,
          gaugedPath g tau eta t 3,1] t ∧
      (∀ i : Fin 6, |gaugeFrame (tau t) (eta t) i| ≤ P^C ∧
        |originalUpperAffineInv (gaugeFrame (tau t) (eta t)) i| ≤ P^C) ∧
      (∀ i j : Fin 4,
        |originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)) i j| ≤ P^C ∧
        |((originalAffineHomogeneousMatrix (gaugeFrame (tau t) (eta t)))⁻¹) i j| ≤ P^C) := by
  let b := originalAffineBodyCoordinates (g t) v
  have hg' : HasDerivAt g (originalUpperBodyVelocity (g t) b) t := by
    simpa only [b,originalUpperBodyVelocity_body] using hg
  have hq := gaugedPath_hasDerivAt g b tau eta t dtau deta hg' ht he htau heta hF
  have hactualBody : originalAffineBodyCoordinates (gaugedPath g tau eta t)
      (deriv (gaugedPath g tau eta) t) = gaugeBodyRates b dtau deta := by
    rw [hq.deriv,originalUpperBodyCoordinates_velocity]
  have hmatrix := originalAffineHomogeneousMatrix_hasDerivAt _ _ t hq
  have hactual : (originalAffineHomogeneousMatrix (gaugedPath g tau eta t))⁻¹ *
      deriv (fun u => originalAffineHomogeneousMatrix (gaugedPath g tau eta u)) t =
        originalAffineHomogeneousVelocity (gaugeBodyRates b dtau deta) := by
    rw [hmatrix.deriv,originalAffineHomogeneousMatrix_body,originalUpperBodyCoordinates_velocity]
  have hs := originalAffineHomogeneousMatrix_hasDerivAt _ _ t
    (gaugeFrame_hasDerivAt tau eta t dtau deta ht he)
  have hB0 : 0 ≤ P^C := Real.rpow_nonneg (by linarith : 0 ≤ P) C
  have hB1 : 1 ≤ P^C := by simpa [hF] using hbody 5
  have htb : |tau t| ≤ P^C := by rw [htau]; exact hbody 2
  have heb : |eta t| ≤ P^C := by rw [heta]; exact hbody 4
  refine ⟨gaugedPath_matrix g tau eta,hq,hactualBody,?_,hactual,?_,?_,?_⟩
  · rw [hactual,hs.deriv,htau,heta]
    exact (gauge_matrix_generator b dtau deta hF).symm
  · convert hq using 1
    ext i
    fin_cases i <;> simp [originalUpperBodyVelocity,gaugeBodyRates,b,heta] <;> ring
  · intro i
    rw [gaugeFrame_inverse]
    fin_cases i <;> simp [gaugeFrame,hB0,htb,heb]
  · intro i j
    rw [originalAffineHomogeneousMatrix_inverse,gaugeFrame_inverse]
    fin_cases i <;> fin_cases j <;>
      simp [originalAffineHomogeneousMatrix,gaugeFrame,hB0,hB1,htb,heb]

end PaperI.OriginalFGauge
