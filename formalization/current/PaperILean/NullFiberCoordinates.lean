import PaperILean.OriginalUpperNormalPullback
import PaperILean.OriginalGaussCoefficientPerturbation
import Mathlib.Tactic

/-! The coordinate-construction stage at manuscript I2375[0,379).
The maps below use the original upper affine coordinates (a,b,c₀,d,e,f).
All coefficient actions are the saved quotient coefficient actions. -/
namespace PaperI.NullFiberCoordinates

open ContinuousLinearMap

abbrev Joint := Fin 6 → ℝ
abbrev Fiber := Fin 4 → ℝ

def jointChange (q : Joint) : Joint :=
  ![q 0, q 1, q 2, q 3, q 4 + q 3 * q 5, q 5]

def jointInverse (h : Joint) : Joint :=
  ![h 0, h 1, h 2, h 3, h 4 - h 3 * h 5, h 5]

def fiberChange (η f : ℝ) (p : Fiber) : Fiber :=
  ![p 0, p 1, p 2 - p 0 * η - p 1 * f, p 3]

def fiberInverse (η f : ℝ) (p : Fiber) : Fiber :=
  ![p 0, p 1, p 2 + p 0 * η + p 1 * f, p 3]

def seed (η f : ℝ) : Joint := ![0, 0, 0, 0, η, f]
def h0 (a : Fiber) : Joint := ![a 0, a 1, a 2, a 3, 0, 0]
def assemble (η f : ℝ) (p : Fiber) : Joint :=
  ![p 0, p 1, p 2, p 3, η + p 3 * f, f]

noncomputable def jointD (q : Joint) : Joint →L[ℝ] Joint :=
  ContinuousLinearMap.pi ![proj 0, proj 1, proj 2, proj 3,
    proj 4 + q 3 • proj 5 + q 5 • proj 3, proj 5]

noncomputable def fiberD (η f : ℝ) : Fiber →L[ℝ] Fiber :=
  ContinuousLinearMap.pi ![proj 0, proj 1,
    proj 2 - η • proj 0 - f • proj 1, proj 3]

def completeJoint (n : ℕ) : (Fin n → ℝ) × Joint → (Fin n → ℝ) × Joint :=
  Prod.map id jointChange

def completeFiber (n : ℕ) (η f : ℝ) :
    (Fin n → ℝ) × Fiber → (Fin n → ℝ) × Fiber :=
  Prod.map id (fiberChange η f)

noncomputable def completeJointD (n : ℕ) (q : Joint) :
    ((Fin n → ℝ) × Joint) →L[ℝ] ((Fin n → ℝ) × Joint) :=
  (ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap (jointD q)

noncomputable def completeFiberD (n : ℕ) (η f : ℝ) :
    ((Fin n → ℝ) × Fiber) →L[ℝ] ((Fin n → ℝ) × Fiber) :=
  (ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap (fiberD η f)

theorem joint_inverses (q : Joint) :
    jointInverse (jointChange q) = q ∧ jointChange (jointInverse q) = q := by
  constructor <;> ext i <;> fin_cases i <;> simp [jointChange, jointInverse]

theorem fiber_inverses (η f : ℝ) (p : Fiber) :
    fiberInverse η f (fiberChange η f p) = p ∧
      fiberChange η f (fiberInverse η f p) = p := by
  constructor <;> ext i <;> fin_cases i <;> simp [fiberChange, fiberInverse] <;> ring

theorem joint_hasFDerivAt (q : Joint) : HasFDerivAt jointChange (jointD q) q := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [jointChange, jointD] using (hasFDerivAt_apply (𝕜 := ℝ) 0 q)
  · simpa [jointChange, jointD] using (hasFDerivAt_apply (𝕜 := ℝ) 1 q)
  · simpa [jointChange, jointD] using (hasFDerivAt_apply (𝕜 := ℝ) 2 q)
  · simpa [jointChange, jointD] using (hasFDerivAt_apply (𝕜 := ℝ) 3 q)
  · simpa [jointChange, jointD, add_assoc] using
      (hasFDerivAt_apply (𝕜 := ℝ) 4 q).add
        ((hasFDerivAt_apply (𝕜 := ℝ) 3 q).mul (hasFDerivAt_apply (𝕜 := ℝ) 5 q))
  · simpa [jointChange, jointD] using (hasFDerivAt_apply (𝕜 := ℝ) 5 q)

theorem fiber_hasFDerivAt (η f : ℝ) (p : Fiber) :
    HasFDerivAt (fiberChange η f) (fiberD η f) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [fiberChange, fiberD] using (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  · simpa [fiberChange, fiberD] using (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  · simpa [fiberChange, fiberD, mul_comm] using
      ((hasFDerivAt_apply (𝕜 := ℝ) 2 p).sub
        ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).const_mul η)).sub
          ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul f)
  · simpa [fiberChange, fiberD] using (hasFDerivAt_apply (𝕜 := ℝ) 3 p)

private theorem det_update_one {n : ℕ} (i : Fin n) (r : Fin n → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin n) (Fin n) ℝ) i r).det = r i := by
  have hr : (∑ j : Fin n, r j • (1 : Matrix (Fin n) (Fin n) ℝ) j) = r := by
    ext k
    simp [Matrix.one_apply, Pi.smul_apply, Finset.sum_apply]
  simpa [hr] using Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) i r

private theorem jointD_matrix (q : Joint) :
    (jointD q).toLinearMap = Matrix.toLin'
      (Matrix.updateRow (1 : Matrix (Fin 6) (Fin 6) ℝ) 4
        ![0, 0, 0, q 5, 1, q 3]) := by
  ext v i
  fin_cases i <;>
    simp [jointD, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Matrix.updateRow, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

private theorem fiberD_matrix (η f : ℝ) :
    (fiberD η f).toLinearMap = Matrix.toLin'
      (Matrix.updateRow (1 : Matrix (Fin 4) (Fin 4) ℝ) 2
        ![-η, -f, 1, 0]) := by
  ext v i
  fin_cases i <;>
    simp [fiberD, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Matrix.updateRow, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

theorem joint_det (q : Joint) : LinearMap.det (jointD q).toLinearMap = 1 := by
  rw [jointD_matrix, LinearMap.det_toLin', det_update_one]
  rfl

theorem fiber_det (η f : ℝ) : LinearMap.det (fiberD η f).toLinearMap = 1 := by
  rw [fiberD_matrix, LinearMap.det_toLin', det_update_one]
  rfl

theorem completeJoint_hasFDerivAt (n : ℕ) (s : Fin n → ℝ) (q : Joint) :
    HasFDerivAt (completeJoint n) (completeJointD n q) (s, q) := by
  exact (hasFDerivAt_id s).prodMap (s, q) (joint_hasFDerivAt q)

theorem completeFiber_hasFDerivAt (n : ℕ) (η f : ℝ) (s : Fin n → ℝ) (p : Fiber) :
    HasFDerivAt (completeFiber n η f) (completeFiberD n η f) (s, p) := by
  exact (hasFDerivAt_id s).prodMap (s, p) (fiber_hasFDerivAt η f p)

theorem completeJoint_det (n : ℕ) (q : Joint) :
    LinearMap.det (completeJointD n q).toLinearMap = 1 := by
  change LinearMap.det (LinearMap.prodMap
    (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (jointD q).toLinearMap) = (1 : ℝ)
  rw [LinearMap.det_prodMap, LinearMap.det_id, joint_det, one_mul]

theorem completeFiber_det (n : ℕ) (η f : ℝ) :
    LinearMap.det (completeFiberD n η f).toLinearMap = 1 := by
  change LinearMap.det (LinearMap.prodMap
    (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (fiberD η f).toLinearMap) = (1 : ℝ)
  rw [LinearMap.det_prodMap, LinearMap.det_id, fiber_det, one_mul]

theorem factor (η f : ℝ) (p : Fiber) :
    originalUpperAffineComp (h0 (fiberChange η f p)) (seed η f) = assemble η f p := by
  ext i
  fin_cases i <;> simp [originalUpperAffineComp, h0, fiberChange, seed, assemble] <;> ring

theorem inverse_factor (η f : ℝ) (p : Fiber) :
    originalUpperAffineInv (assemble η f p) =
      originalUpperAffineComp (originalUpperAffineInv (seed η f))
        (originalUpperAffineInv (h0 (fiberChange η f p))) := by
  ext i
  fin_cases i <;>
    simp [originalUpperAffineInv, originalUpperAffineComp, assemble, seed, h0, fiberChange] <;> ring

theorem single_fiber (η f : ℝ) (h : Joint) :
    (h 4 - h 3 * h 5 = η ∧ h 5 = f) ↔
      ∃! a : Fiber, h = originalUpperAffineComp (h0 a) (seed η f) := by
  constructor
  · rintro ⟨hη, hf⟩
    refine ⟨![h 0, h 1, h 2 - h 0 * η - h 1 * f, h 3], ?_, ?_⟩
    · ext i
      fin_cases i <;> simp [originalUpperAffineComp, h0, seed]
      · ring
      · rw [← hf, ← hη]
        ring
      · exact hf
    · intro a ha
      have ha0 := congrFun ha 0
      have ha1 := congrFun ha 1
      have ha2 := congrFun ha 2
      have ha3 := congrFun ha 3
      simp [originalUpperAffineComp, h0, seed] at ha0 ha1 ha2 ha3
      ext i
      fin_cases i <;> simp [← ha0, ← ha1, ← ha3]
      rw [← ha0, ← ha1] at ha2
      linarith
  · rintro ⟨a, rfl, _⟩
    simp [originalUpperAffineComp, h0, seed]

theorem inverse_coefficient_action {k : ℕ} (J : CoefficientSpace k) (η f : ℝ) (p : Fiber) :
    originalUpperCoefficientPullback J (originalUpperAffineInv (assemble η f p)) =
      originalUpperCoefficientPullback
        (originalUpperCoefficientPullback J (originalUpperAffineInv (seed η f)))
        (originalUpperAffineInv (h0 (fiberChange η f p))) := by
  rw [originalUpperCoefficientPullback_comp, inverse_factor]

theorem coefficient_zero {k : ℕ} (F : CoefficientSpace k) :
    originalUpperCoefficientPullback F (0 : Joint) = F := by
  have hm : originalUpperLinearMatrix (0 : Joint) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [originalUpperLinearMatrix, Matrix.one_apply]
  have hz : (![0, 0, 0] : Fin 3 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
  simpa [originalUpperCoefficientPullback, hm, hz] using affineCoefficientMap_identity k F

theorem coefficient_reconstruction {k : ℕ} (F : CoefficientSpace k) (h : Joint) :
    originalUpperCoefficientPullback (originalUpperCoefficientPullback F h)
      (originalUpperAffineInv h) = F := by
  rw [originalUpperCoefficientPullback_comp, (originalUpperAffineComp_inv h).2,
    coefficient_zero]

theorem fixed_frame_reconstruction {k : ℕ} (F : CoefficientSpace k) (η f : ℝ) (p : Fiber) :
    originalUpperCoefficientPullback
      (originalUpperCoefficientPullback
        (originalUpperCoefficientPullback F (assemble η f p))
        (originalUpperAffineInv (seed η f)))
      (originalUpperAffineInv (h0 (fiberChange η f p))) = F := by
  rw [← inverse_coefficient_action, coefficient_reconstruction]

/-- Complete coordinate and single-fiber construction, with untouched slice coordinates,
actual derivatives, signed unit Jacobians, and the actual quotient coefficient action.
No multiplicity, Haar, density, or subsequent transverse-Jacobian claim is asserted. -/
theorem null_fiber_coordinates_stage (n k : ℕ) (η f : ℝ)
    (F : CoefficientSpace k) (q : Joint) (p : Fiber) (s : Fin n → ℝ) :
    (jointInverse (jointChange q) = q ∧ jointChange (jointInverse q) = q) ∧
    HasFDerivAt jointChange (jointD q) q ∧ LinearMap.det (jointD q).toLinearMap = 1 ∧
    (fiberInverse η f (fiberChange η f p) = p ∧
      fiberChange η f (fiberInverse η f p) = p) ∧
    HasFDerivAt (fiberChange η f) (fiberD η f) p ∧
    LinearMap.det (fiberD η f).toLinearMap = 1 ∧
    HasFDerivAt (completeJoint n) (completeJointD n q) (s, q) ∧
    LinearMap.det (completeJointD n q).toLinearMap = 1 ∧
    HasFDerivAt (completeFiber n η f) (completeFiberD n η f) (s, p) ∧
    LinearMap.det (completeFiberD n η f).toLinearMap = 1 ∧
    (∀ h : Joint, (h 4 - h 3 * h 5 = η ∧ h 5 = f) ↔
      ∃! a : Fiber, h = originalUpperAffineComp (h0 a) (seed η f)) ∧
    originalUpperAffineComp (h0 (fiberChange η f p)) (seed η f) = assemble η f p ∧
    originalUpperAffineInv (assemble η f p) =
      originalUpperAffineComp (originalUpperAffineInv (seed η f))
        (originalUpperAffineInv (h0 (fiberChange η f p))) ∧
    originalUpperCoefficientPullback (originalUpperCoefficientPullback F (assemble η f p))
      (originalUpperAffineInv (assemble η f p)) = F ∧
    originalUpperCoefficientPullback
      (originalUpperCoefficientPullback
        (originalUpperCoefficientPullback F (assemble η f p))
        (originalUpperAffineInv (seed η f)))
      (originalUpperAffineInv (h0 (fiberChange η f p))) = F := by
  exact ⟨joint_inverses q, joint_hasFDerivAt q, joint_det q, fiber_inverses η f p,
    fiber_hasFDerivAt η f p, fiber_det η f, completeJoint_hasFDerivAt n s q,
    completeJoint_det n q, completeFiber_hasFDerivAt n η f s p, completeFiber_det n η f,
    single_fiber η f, factor η f p, inverse_factor η f p,
    coefficient_reconstruction F _, fixed_frame_reconstruction F η f p⟩

end PaperI.NullFiberCoordinates
