import PaperILean.AffineNormalizationMatrices
import PaperILean.OriginalUpperBodyFlow
import PaperILean.OriginalGaussRelativeFrameIntegration

/-! I1495[248,449), I1496-I1498: exact anisotropic normalization of the
actual original relative path and its six body coefficients. Spatial
scales and the anchor are fixed during differentiation. -/

noncomputable section
namespace PaperI.OriginalUpperNormalization
open AffineNormalizationMatrices

noncomputable def Phi (sx sy sz : ℝ) (q : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q 0*sy/sx, q 1*sz/sx, q 2/sx, q 3*sz/sy, q 4/sy, q 5/sz]

noncomputable def normalizedUpperPath (g : ℝ → Fin 6 → ℝ)
    (t0 h sx sy sz : ℝ) (s : ℝ) : Fin 6 → ℝ :=
  Phi sx sy sz (originalUpperRelativeFrame (g t0) (g (t0+h*s)))

noncomputable def normalizedBodyRates (h sx sy sz : ℝ) (xi : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![h*xi 0*sy/sx, h*xi 1*sz/sx, h*xi 2/sx,
    h*xi 3*sz/sy, h*xi 4/sy, h*xi 5/sz]

theorem Phi_zero (sx sy sz : ℝ) : Phi sx sy sz 0 = 0 := by
  ext i
  fin_cases i <;> simp [Phi]

theorem Phi_smul (sx sy sz r : ℝ) (q : Fin 6 → ℝ) :
    Phi sx sy sz (r • q) = r • Phi sx sy sz q := by
  ext i
  fin_cases i <;> simp [Phi] <;> ring

theorem normalizedBodyRates_eq_smul (h sx sy sz : ℝ) (xi : Fin 6 → ℝ) :
    normalizedBodyRates h sx sy sz xi = h • Phi sx sy sz xi := by
  ext i
  fin_cases i <;> simp [normalizedBodyRates, Phi] <;> ring

theorem Phi_hasDerivAt (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (sx sy sz t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun u => Phi sx sy sz (g u)) (Phi sx sy sz v) t := by
  have hi := hasDerivAt_pi.mp hg
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [Phi] using ((hi 0).mul_const sy).div_const sx
  · simpa [Phi] using ((hi 1).mul_const sz).div_const sx
  · simpa [Phi] using (hi 2).div_const sx
  · simpa [Phi] using ((hi 3).mul_const sz).div_const sy
  · simpa [Phi] using (hi 4).div_const sy
  · simpa [Phi] using (hi 5).div_const sz

theorem originalUpperBodyVelocity_smul (q xi : Fin 6 → ℝ) (r : ℝ) :
    originalUpperBodyVelocity q (r • xi) = r • originalUpperBodyVelocity q xi := by
  ext i
  fin_cases i <;> simp [originalUpperBodyVelocity] <;> ring

theorem Phi_bodyVelocity (sx sy sz : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0)
    (hsz : sz ≠ 0) (q xi : Fin 6 → ℝ) :
    Phi sx sy sz (originalUpperBodyVelocity q xi) =
      originalUpperBodyVelocity (Phi sx sy sz q) (Phi sx sy sz xi) := by
  ext i
  fin_cases i <;> simp [Phi, originalUpperBodyVelocity]
    <;> field_simp <;> ring

theorem Phi_homogeneousMatrix (sx sy sz : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0)
    (hsz : sz ≠ 0) (q : Fin 6 → ℝ) :
    originalAffineHomogeneousMatrix (Phi sx sy sz q) =
      (homogeneousDiagonal sx sy sz)⁻¹ * originalAffineHomogeneousMatrix q *
        homogeneousDiagonal sx sy sz := by
  rw [homogeneousDiagonal_inverse sx sy sz hsx hsy hsz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi, originalAffineHomogeneousMatrix, homogeneousDiagonal,
      Matrix.mul_apply, Fin.sum_univ_succ, hsx, hsy, hsz] <;> ring

theorem normalizedUpperPath_matrix (g : ℝ → Fin 6 → ℝ)
    (t0 h sx sy sz : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0) (hsz : sz ≠ 0) (s : ℝ) :
    originalAffineHomogeneousMatrix (normalizedUpperPath g t0 h sx sy sz s) =
      normalizedMatrixPath (fun t => originalAffineHomogeneousMatrix (g t))
        t0 h sx sy sz s := by
  rw [normalizedUpperPath, Phi_homogeneousMatrix sx sy sz hsx hsy hsz,
    ← originalAffineHomogeneousMatrix_relative]
  simp only [normalizedMatrixPath, Matrix.mul_assoc]

theorem normalizedUpperPath_zero (g : ℝ → Fin 6 → ℝ) (t0 h sx sy sz : ℝ) :
    normalizedUpperPath g t0 h sx sy sz 0 = 0 := by
  simp only [normalizedUpperPath, mul_zero, add_zero, originalUpperRelativeFrame_self, Phi_zero]

theorem normalizedUpperPath_hasDerivAt (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (t0 h sx sy sz s : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0) (hsz : sz ≠ 0)
    (hg : HasDerivAt g v (t0+h*s)) :
    HasDerivAt (normalizedUpperPath g t0 h sx sy sz)
      (originalUpperBodyVelocity (normalizedUpperPath g t0 h sx sy sz s)
        (normalizedBodyRates h sx sy sz (originalAffineBodyCoordinates (g (t0+h*s)) v))) s := by
  have htime : HasDerivAt (fun u : ℝ => t0+h*u) h s := by
    simpa using ((hasDerivAt_id s).const_mul h).const_add t0
  have hrel := originalUpperRelativeFrame_body_derivative g (g t0) v (t0+h*s) hg
  have hc := hrel.scomp s htime
  have hp := Phi_hasDerivAt _ _ sx sy sz s hc
  simpa only [Function.comp_def, Phi_smul, Phi_bodyVelocity sx sy sz hsx hsy hsz,
    normalizedBodyRates_eq_smul, originalUpperBodyVelocity_smul, normalizedUpperPath] using hp

theorem normalizedUpperPath_body (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (t0 h sx sy sz s : ℝ) (hsx : sx ≠ 0) (hsy : sy ≠ 0) (hsz : sz ≠ 0)
    (hg : HasDerivAt g v (t0+h*s)) :
    originalAffineBodyCoordinates (normalizedUpperPath g t0 h sx sy sz s)
      (deriv (normalizedUpperPath g t0 h sx sy sz) s) =
      normalizedBodyRates h sx sy sz (originalAffineBodyCoordinates (g (t0+h*s)) v) := by
  rw [(normalizedUpperPath_hasDerivAt g v t0 h sx sy sz s hsx hsy hsz hg).deriv,
    originalUpperBodyCoordinates_velocity]

/-- The source setup and all six exact normalized body rates for the actual
relative path. The first conjunct identifies its computational coordinates
with the literal homogeneous matrix path at every parameter value. -/
theorem original_upper_normalization_stage (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (t0 theta H sx sy sz s : ℝ)
    (_htheta0 : 0 < theta) (_htheta1 : theta < 1) (_hH : 1 ≤ H)
    (hsx : 0 < sx) (hsy : 0 < sy) (hsz : 0 < sz)
    (hg : HasDerivAt g v (t0+(theta*H)*s)) :
    (∀ u, originalAffineHomogeneousMatrix (normalizedUpperPath g t0 (theta*H) sx sy sz u) =
      normalizedMatrixPath (fun t => originalAffineHomogeneousMatrix (g t))
        t0 (theta*H) sx sy sz u) ∧
    normalizedUpperPath g t0 (theta*H) sx sy sz 0 = 0 ∧
    HasDerivAt (normalizedUpperPath g t0 (theta*H) sx sy sz)
      (originalUpperBodyVelocity (normalizedUpperPath g t0 (theta*H) sx sy sz s)
        (normalizedBodyRates (theta*H) sx sy sz
          (originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v))) s ∧
    originalAffineBodyCoordinates (normalizedUpperPath g t0 (theta*H) sx sy sz s)
      (deriv (normalizedUpperPath g t0 (theta*H) sx sy sz) s) =
      ![(theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 0*sy/sx,
        (theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 1*sz/sx,
        (theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 2/sx,
        (theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 3*sz/sy,
        (theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 4/sy,
        (theta*H)*(originalAffineBodyCoordinates (g (t0+(theta*H)*s)) v) 5/sz] := by
  exact ⟨normalizedUpperPath_matrix g t0 (theta*H) sx sy sz hsx.ne' hsy.ne' hsz.ne',
    normalizedUpperPath_zero g t0 (theta*H) sx sy sz,
    normalizedUpperPath_hasDerivAt g v t0 (theta*H) sx sy sz s hsx.ne' hsy.ne' hsz.ne' hg,
    normalizedUpperPath_body g v t0 (theta*H) sx sy sz s hsx.ne' hsy.ne' hsz.ne' hg⟩

end PaperI.OriginalUpperNormalization
