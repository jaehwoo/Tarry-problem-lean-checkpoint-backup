import PaperILean.OriginalGaussBodyPathBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! I1305: left-normalization removes the initial shear without changing body velocity.
The six coordinates are A,C,Tx,D,Ty,Tz; the identity is the zero vector. -/
noncomputable section
namespace PaperI

def originalUpperBodyVelocity (g b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![b 0, b 1 + g 0 * b 3, b 2 + g 0 * b 4 + g 1 * b 5,
    b 3, b 4 + g 3 * b 5, b 5]

def originalUpperRelativeFrame (g₀ g : Fin 6 → ℝ) : Fin 6 → ℝ :=
  originalUpperAffineComp (originalUpperAffineInv g₀) g

theorem originalUpperBodyVelocity_body (g v : Fin 6 → ℝ) :
    originalUpperBodyVelocity g (originalAffineBodyCoordinates g v) = v := by
  ext i
  fin_cases i <;> simp [originalUpperBodyVelocity, originalAffineBodyCoordinates] <;> ring

theorem originalUpperBodyCoordinates_velocity (g b : Fin 6 → ℝ) :
    originalAffineBodyCoordinates g (originalUpperBodyVelocity g b) = b := by
  ext i
  fin_cases i <;> simp [originalUpperBodyVelocity, originalAffineBodyCoordinates] <;> ring

theorem originalUpperRelativeFrame_self (g : Fin 6 → ℝ) :
    originalUpperRelativeFrame g g = 0 :=
  (originalUpperAffineComp_inv g).1

theorem originalUpperRelativeFrame_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (g₀ b : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g (originalUpperBodyVelocity (g t) b) t) :
    HasDerivAt (fun s => originalUpperRelativeFrame g₀ (g s))
      (originalUpperBodyVelocity (originalUpperRelativeFrame g₀ (g t)) b) t := by
  have h := hasDerivAt_pi.mp hg
  simp only [originalUpperBodyVelocity, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
      originalUpperBodyVelocity] using (h 0).const_add (-g₀ 0)
  · convert ((h 1).const_add (g₀ 0 * g₀ 3 - g₀ 1)).add
      ((h 3).const_mul (-g₀ 0)) using 1 <;>
      simp [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
        originalUpperBodyVelocity] <;> ring
  · convert (((h 2).const_add (-g₀ 2 + g₀ 0 * g₀ 4 + g₀ 1 * g₀ 5 -
      g₀ 0 * g₀ 3 * g₀ 5)).add ((h 4).const_mul (-g₀ 0))).add
        ((h 5).const_mul (g₀ 0 * g₀ 3 - g₀ 1)) using 1 <;>
      simp [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
        originalUpperBodyVelocity] <;> ring
  · simpa [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
      originalUpperBodyVelocity] using (h 3).const_add (-g₀ 3)
  · convert ((h 4).const_add (g₀ 3 * g₀ 5 - g₀ 4)).add
      ((h 5).const_mul (-g₀ 3)) using 1 <;>
      simp [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
        originalUpperBodyVelocity] <;> ring
  · simpa [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv,
      originalUpperBodyVelocity] using (h 5).const_add (-g₀ 5)

theorem originalUpperRelativeFrame_body_derivative
    (g : ℝ → Fin 6 → ℝ) (g₀ v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => originalUpperRelativeFrame g₀ (g s))
      (originalUpperBodyVelocity (originalUpperRelativeFrame g₀ (g t))
        (originalAffineBodyCoordinates (g t) v)) t := by
  apply originalUpperRelativeFrame_hasDerivAt
  simpa only [originalUpperBodyVelocity_body] using hg

end PaperI
