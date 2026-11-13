import PaperILean.OriginalGaussBodyCalculus

/-! I1293/I1297: the literal homogeneous affine matrix and its body velocity.
Coordinate order is A,C,Tx,D,Ty,Tz = (a,b,c,d,e,f). -/
noncomputable section
namespace PaperI

def originalAffineHomogeneousMatrix (g : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,g 0,g 1,g 2; 0,1,g 3,g 4; 0,0,1,g 5; 0,0,0,1]
def originalAffineHomogeneousVelocity (v : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,v 0,v 1,v 2; 0,0,v 3,v 4; 0,0,0,v 5; 0,0,0,0]
def originalAffineBodyCoordinates (g v : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![v 0,v 1-g 0*v 3,v 2-g 0*v 4+(g 0*g 3-g 1)*v 5,
    v 3,v 4-g 3*v 5,v 5]

theorem originalAffineHomogeneousMatrix_eval (g : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    (originalAffineHomogeneousMatrix g).mulVec ![x 0,x 1,x 2,1] =
      ![originalUpperAffineEval g x 0,originalUpperAffineEval g x 1,
        originalUpperAffineEval g x 2,1] := by
  ext i
  fin_cases i <;> simp [originalAffineHomogeneousMatrix,originalUpperAffineEval,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem originalAffineHomogeneousMatrix_inverse (g : Fin 6 → ℝ) :
    (originalAffineHomogeneousMatrix g)⁻¹ =
      originalAffineHomogeneousMatrix (originalUpperAffineInv g) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalAffineHomogeneousMatrix,originalUpperAffineInv,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply] <;> ring

theorem originalAffineHomogeneousMatrix_body (g v : Fin 6 → ℝ) :
    (originalAffineHomogeneousMatrix g)⁻¹ * originalAffineHomogeneousVelocity v =
      originalAffineHomogeneousVelocity (originalAffineBodyCoordinates g v) := by
  rw [originalAffineHomogeneousMatrix_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalAffineHomogeneousMatrix,originalAffineHomogeneousVelocity,
      originalUpperAffineInv,originalAffineBodyCoordinates,Matrix.mul_apply,Fin.sum_univ_succ]
    <;> ring

theorem originalAffineHomogeneousMatrix_hasDerivAt
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => originalAffineHomogeneousMatrix (g s))
      (originalAffineHomogeneousVelocity v) t := by
  have h := hasDerivAt_pi.mp hg
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
    <;> first | exact h _ | exact hasDerivAt_const t _

theorem originalAffineHomogeneousMatrix_body_derivative
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t) :
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ,
      HasDerivAt (fun s => originalAffineHomogeneousMatrix (g s)) M t ∧
      (originalAffineHomogeneousMatrix (g t))⁻¹ * M =
        originalAffineHomogeneousVelocity (originalAffineBodyCoordinates (g t) v) := by
  exact ⟨_,originalAffineHomogeneousMatrix_hasDerivAt g v t hg,
    originalAffineHomogeneousMatrix_body (g t) v⟩

end PaperI
