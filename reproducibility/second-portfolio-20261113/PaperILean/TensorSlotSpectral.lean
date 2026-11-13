import PaperILean.TensorSlotAction

/-! Orthogonal reduction of the actual slot action. This proves its
HS self-adjointness for symmetric H without assuming symmetry of the tensor. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem tensorOneSlotAction_pullback {r : ℕ} (T : TensorSpace r)
    (H K A : Matrix (Fin 3) (Fin 3) ℝ) (h : H * A = A * K) (j : Fin r) :
    tensorFramePullback (tensorOneSlotAction H j T) A =
      tensorOneSlotAction K j (tensorFramePullback T A) := by
  ext v
  simp only [tensorFramePullback_apply, tensorOneSlotAction_apply]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    simp only [Function.update_self, Matrix.mulVec_mulVec]
    rw [h]
  · simp only [Function.update_of_ne hi]

theorem tensorSlotAction_pullback {r : ℕ} (T : TensorSpace r)
    (H K A : Matrix (Fin 3) (Fin 3) ℝ) (h : H * A = A * K) :
    tensorFramePullback (tensorSlotAction H T) A = tensorSlotAction K (tensorFramePullback T A) := by
  ext v
  simp only [tensorFramePullback_apply, tensorSlotAction, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun S : TensorSpace r => S v) (tensorOneSlotAction_pullback T H K A h j)

theorem tensorOneSlotAction_diagonal_coordinates {r : ℕ} (T : TensorSpace r)
    (d : Fin 3 → ℝ) (j : Fin r) (a : Fin r → Fin 3) :
    tensorCoordinates (tensorOneSlotAction (Matrix.diagonal d) j T) a =
      d (a j) * tensorCoordinates T a := by
  have hv : Matrix.diagonal d *ᵥ (Pi.single (a j) (1 : ℝ) : PhysicalSpace) =
      d (a j) • (Pi.single (a j) (1 : ℝ) : PhysicalSpace) := by
    ext i
    by_cases hi : i = a j
    · subst i
      simp [Matrix.mulVec_single_one, Matrix.diagonal_apply, Pi.single_apply]
    · simp [Matrix.mulVec_single_one, Matrix.diagonal_apply, Pi.single_apply, hi, Ne.symm hi]
  simp only [tensorCoordinates, tensorOneSlotAction_apply, hv]
  rw [T.map_update_smul]
  simp only [Function.update_eq_self, smul_eq_mul]

theorem tensorSlotAction_diagonal_coordinates {r : ℕ} (T : TensorSpace r)
    (d : Fin 3 → ℝ) (a : Fin r → Fin 3) :
    tensorCoordinates (tensorSlotAction (Matrix.diagonal d) T) a =
      (∑ j, d (a j)) * tensorCoordinates T a := by
  simp only [tensorCoordinates, tensorSlotAction, ContinuousMultilinearMap.sum_apply]
  change (∑ j, tensorCoordinates (tensorOneSlotAction (Matrix.diagonal d) j T) a) = _
  simp only [tensorOneSlotAction_diagonal_coordinates, Finset.sum_mul]
  rfl

theorem symmetricFrame_eigenbasis_intertwines
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    H * (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ) =
      (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ) *
        Matrix.diagonal (symmetricFrameEigenvalues H hH) := by
  conv_lhs => arg 1; rw [symmetricFrame_spectral H hH]
  simp only [orthogonalConjugate, Matrix.mul_assoc]
  have hu := unitary.coe_star_mul_self (symmetricFrameEigenbasis H hH)
  change star (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ) *
    (symmetricFrameEigenbasis H hH : Matrix (Fin 3) (Fin 3) ℝ) = 1 at hu
  rw [hu, Matrix.mul_one]

theorem tensorSlotAction_selfAdjoint {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsSymm) (T S : TensorSpace r) :
    tensorHSInner (tensorSlotAction H T) S = tensorHSInner T (tensorSlotAction H S) := by
  let U := symmetricFrameEigenbasis H hH
  have hU := real_unitary_mul_transpose U
  rw [← tensorHSInner_orthogonal_frame _ _ _ hU, ← tensorHSInner_orthogonal_frame T _ _ hU]
  rw [tensorSlotAction_pullback T H _ _ (symmetricFrame_eigenbasis_intertwines H hH),
    tensorSlotAction_pullback S H _ _ (symmetricFrame_eigenbasis_intertwines H hH)]
  simp only [tensorHSInner, tensorSlotAction_diagonal_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  ring

end PaperI
