import PaperILean.AffineJetDerivatives

/-! Physical affine entries of the augmented state (manuscript I:595–607).
The physical constant coefficient is retained. No matrix is required to be invertible.
The explicit norm uses Euclidean translation and Hilbert–Schmidt matrix squares.
-/

open scoped BigOperators
open Matrix

noncomputable section
namespace PaperI

abbrev PhysicalAffineData := PhysicalSpace × Matrix (Fin 3) (Fin 3) ℝ

def upperAffineFieldTranslation (ξ : Fin 6 → ℝ) : PhysicalSpace :=
  ![ξ 2, ξ 4, ξ 5]

def upperAffineFieldLinear (ξ : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, ξ 0, ξ 1; 0, 0, ξ 3; 0, 0, 0]

theorem upperAffineFieldTranslation_zero : upperAffineFieldTranslation 0 = 0 := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation]

theorem upperAffineFieldTranslation_add (ξ ζ : Fin 6 → ℝ) :
    upperAffineFieldTranslation (ξ + ζ) =
      upperAffineFieldTranslation ξ + upperAffineFieldTranslation ζ := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation]

theorem upperAffineFieldTranslation_smul (r : ℝ) (ξ : Fin 6 → ℝ) :
    upperAffineFieldTranslation (r • ξ) = r • upperAffineFieldTranslation ξ := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation]

theorem upperAffineFieldLinear_zero : upperAffineFieldLinear 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperAffineFieldLinear]

theorem upperAffineFieldLinear_add (ξ ζ : Fin 6 → ℝ) :
    upperAffineFieldLinear (ξ + ζ) =
      upperAffineFieldLinear ξ + upperAffineFieldLinear ζ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperAffineFieldLinear]

theorem upperAffineFieldLinear_smul (r : ℝ) (ξ : Fin 6 → ℝ) :
    upperAffineFieldLinear (r • ξ) = r • upperAffineFieldLinear ξ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperAffineFieldLinear]

theorem upperAffineField_coordinates_injective : Function.Injective
    (fun ξ => (upperAffineFieldTranslation ξ, upperAffineFieldLinear ξ)) := by
  intro ξ ζ h
  have ht := congrArg Prod.fst h
  have hl := congrArg Prod.snd h
  funext i
  fin_cases i
  · simpa [upperAffineFieldLinear] using congrFun (congrFun hl 0) 1
  · simpa [upperAffineFieldLinear] using congrFun (congrFun hl 0) 2
  · simpa [upperAffineFieldTranslation] using congrFun ht 0
  · simpa [upperAffineFieldLinear] using congrFun (congrFun hl 1) 2
  · simpa [upperAffineFieldTranslation] using congrFun ht 1
  · simpa [upperAffineFieldTranslation] using congrFun ht 2

def physicalAffineEval (ell : PhysicalAffineData) (x : PhysicalSpace) : PhysicalSpace :=
  ell.1 + ell.2 *ᵥ x

def physicalAffineFieldAction (ell : PhysicalAffineData) (t : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) : PhysicalAffineData :=
  (ell.2 *ᵥ t, ell.2 * N)

theorem physicalAffineFieldAction_zero (ell : PhysicalAffineData) :
    physicalAffineFieldAction ell 0 0 = 0 := by
  simp [physicalAffineFieldAction]

theorem physicalAffineFieldAction_add (ell : PhysicalAffineData)
    (t u : PhysicalSpace) (N K : Matrix (Fin 3) (Fin 3) ℝ) :
    physicalAffineFieldAction ell (t + u) (N + K) =
      physicalAffineFieldAction ell t N + physicalAffineFieldAction ell u K := by
  simp [physicalAffineFieldAction, Matrix.mulVec_add, mul_add]

theorem physicalAffineFieldAction_smul (ell : PhysicalAffineData) (r : ℝ)
    (t : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    physicalAffineFieldAction ell (r • t) (r • N) =
      r • physicalAffineFieldAction ell t N := by
  simp [physicalAffineFieldAction, Matrix.mulVec_smul, Matrix.mul_smul]

theorem physicalAffineFieldAction_eval (ell : PhysicalAffineData)
    (t x : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    physicalAffineEval (physicalAffineFieldAction ell t N) x =
      ell.2 *ᵥ (t + N *ᵥ x) := by
  simp [physicalAffineEval, physicalAffineFieldAction, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]

theorem hasFDerivAt_physicalAffineEval (ell : PhysicalAffineData) (x : PhysicalSpace) :
    HasFDerivAt (physicalAffineEval ell) (frameLinearMap ell.2) x := by
  exact hasFDerivAt_affinePoint ell.1 ell.2 x

theorem fderiv_physicalAffineEval_field (ell : PhysicalAffineData)
    (t x : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    fderiv ℝ (physicalAffineEval ell) x (t + N *ᵥ x) =
      physicalAffineEval (physicalAffineFieldAction ell t N) x := by
  rw [(hasFDerivAt_physicalAffineEval ell x).fderiv, frameLinearMap_apply,
    physicalAffineFieldAction_eval]

theorem physicalAffineFieldAction_translation (ell : PhysicalAffineData)
    (h : PhysicalSpace) : physicalAffineFieldAction ell h 0 = (ell.2 *ᵥ h, 0) := by
  simp [physicalAffineFieldAction]

theorem physicalAffineEval_translationAction (ell : PhysicalAffineData)
    (h x : PhysicalSpace) :
    physicalAffineEval (physicalAffineFieldAction ell h 0) x = ell.2 *ᵥ h := by
  simp [physicalAffineFieldAction_translation, physicalAffineEval]

theorem upperAffineField_eval_A (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 0 1) +
      upperAffineFieldLinear (Pi.single 0 1) *ᵥ x = ![x 1, 0, 0] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperAffineField_eval_C (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 1 1) +
      upperAffineFieldLinear (Pi.single 1 1) *ᵥ x = ![x 2, 0, 0] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperAffineField_eval_Tx (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 2 1) +
      upperAffineFieldLinear (Pi.single 2 1) *ᵥ x = ![1, 0, 0] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperAffineField_eval_D (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 3 1) +
      upperAffineFieldLinear (Pi.single 3 1) *ᵥ x = ![0, x 2, 0] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperAffineField_eval_Ty (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 4 1) +
      upperAffineFieldLinear (Pi.single 4 1) *ᵥ x = ![0, 1, 0] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperAffineField_eval_Tz (x : PhysicalSpace) :
    upperAffineFieldTranslation (Pi.single 5 1) +
      upperAffineFieldLinear (Pi.single 5 1) *ᵥ x = ![0, 0, 1] := by
  ext i; fin_cases i <;> simp [upperAffineFieldTranslation, upperAffineFieldLinear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def physicalAffineNorm (ell : PhysicalAffineData) : ℝ :=
  Real.sqrt ((∑ i, ell.1 i ^ 2) + ∑ i, ∑ j, ell.2 i j ^ 2)

theorem physicalAffineNorm_nonneg (ell : PhysicalAffineData) :
    0 ≤ physicalAffineNorm ell := Real.sqrt_nonneg _

theorem physicalAffineNorm_sq (ell : PhysicalAffineData) :
    physicalAffineNorm ell ^ 2 = (∑ i, ell.1 i ^ 2) + ∑ i, ∑ j, ell.2 i j ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem physicalAffineNorm_zero : physicalAffineNorm 0 = 0 := by
  simp [physicalAffineNorm]

theorem physicalAffineNorm_translationAction_sq (ell : PhysicalAffineData)
    (h : PhysicalSpace) :
    physicalAffineNorm (physicalAffineFieldAction ell h 0) ^ 2 =
      ∑ i, (ell.2 *ᵥ h) i ^ 2 := by
  rw [physicalAffineNorm_sq, physicalAffineFieldAction_translation]
  simp

theorem physicalAffineNorm_eq_zero_iff (ell : PhysicalAffineData) :
    physicalAffineNorm ell = 0 ↔ ell = 0 := by
  constructor
  · intro h
    have hsum := physicalAffineNorm_sq ell
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hsum
    have hpnonneg : 0 ≤ ∑ i, ell.1 i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hmnonneg : 0 ≤ ∑ i, ∑ j, ell.2 i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have hp : ∑ i, ell.1 i ^ 2 = 0 := by linarith
    have hm : ∑ i, ∑ j, ell.2 i j ^ 2 = 0 := by linarith
    apply Prod.ext
    · funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ell.1 i))).mp hp i (Finset.mem_univ i)
      simpa using hi
    · funext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (ell.2 i j)))).mp hm i (Finset.mem_univ i)
      have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (ell.2 i j))).mp hi j (Finset.mem_univ j)
      simpa using hij
  · rintro rfl
    exact physicalAffineNorm_zero

end PaperI
