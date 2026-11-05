import PaperILean.AugmentedOrbitStatePolynomials
import PaperILean.RankOnePositivity
import PaperILean.OrderedSingularValueContinuity
import Mathlib.Topology.Algebra.MvPolynomial

/-! The full twelve-coordinate affine field and its actual augmented action.
The phase map differentiates before removing the constant term. All physical
translation and matrix coefficients are retained. -/
noncomputable section
namespace PaperI.AffineConditioning
open Matrix
open scoped BigOperators

abbrev FieldIndex := Fin 3 × Fin 4

def fieldTranslation (f : FieldIndex → ℝ) : PhysicalSpace := fun i => f (i, Fin.last 3)
def fieldLinear (f : FieldIndex → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => f (i, j.castSucc)
def fieldMatrix (f : FieldIndex → ℝ) : Matrix (Fin 3) (Fin 4) ℝ := fun i j => f (i,j)
def fieldNorm (f : FieldIndex → ℝ) : ℝ := coordinateL2Norm f

theorem fieldMatrix_reconstruction (f : FieldIndex → ℝ) :
    RankOneAffineMatrix.affineFieldMatrix (fieldTranslation f) (fieldLinear f) = fieldMatrix f := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · exact RankOneAffineMatrix.affineFieldMatrix_last (fieldTranslation f) (fieldLinear f) i
  · exact RankOneAffineMatrix.affineFieldMatrix_castSucc (fieldTranslation f) (fieldLinear f) i _

theorem fieldNorm_eq_frobenius (f : FieldIndex → ℝ) :
    fieldNorm f = RankOneAffineMatrix.affineFieldFrobenius (fieldTranslation f) (fieldLinear f) := by
  rw [RankOneAffineMatrix.affineFieldFrobenius, fieldMatrix_reconstruction]
  simp only [fieldNorm, coordinateL2Norm, Fintype.sum_prod_type, fieldMatrix]

theorem fieldNorm_single (j : FieldIndex) : fieldNorm (Pi.single j 1) = 1 := by
  simp [fieldNorm, coordinateL2Norm, Pi.single_apply]

@[simp] theorem fieldTranslation_of_matrix (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    fieldTranslation (fun ij => RankOneAffineMatrix.affineFieldMatrix b N ij.1 ij.2) = b := by
  ext i
  exact RankOneAffineMatrix.affineFieldMatrix_last b N i

@[simp] theorem fieldLinear_of_matrix (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    fieldLinear (fun ij => RankOneAffineMatrix.affineFieldMatrix b N ij.1 ij.2) = N := by
  ext i j
  exact RankOneAffineMatrix.affineFieldMatrix_castSucc b N i j

def actualAction (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) : AugmentedState k :=
  (affineFieldCoefficientMap k (fieldTranslation f) (fieldLinear f) S.1,
    physicalAffineFieldAction S.2 (fieldTranslation f) (fieldLinear f))

def gap (k : ℕ) (S : AugmentedState k) (f : FieldIndex → ℝ) : ℝ :=
  max (coefficientEuclideanNorm (actualAction k S f).1 +
    physicalAffineNorm (actualAction k S f).2)
    (descendingSingularValues (fieldMatrix f) (1 : Fin 4))

def actualActionFieldMap (k : ℕ) (S : AugmentedState k) :
    (FieldIndex → ℝ) →ₗ[ℝ] AugmentedState k where
  toFun := actualAction k S
  map_add' f g := by
    change (affineFieldCoefficientMap k (fieldTranslation f + fieldTranslation g)
        (fieldLinear f + fieldLinear g) S.1,
      physicalAffineFieldAction S.2 (fieldTranslation f + fieldTranslation g)
        (fieldLinear f + fieldLinear g)) = _
    rw [affineFieldCoefficientMap_add_field, physicalAffineFieldAction_add]
    rfl
  map_smul' a f := by
    change (affineFieldCoefficientMap k (a • fieldTranslation f) (a • fieldLinear f) S.1,
      physicalAffineFieldAction S.2 (a • fieldTranslation f) (a • fieldLinear f)) = _
    rw [affineFieldCoefficientMap_smul_field, physicalAffineFieldAction_smul]
    rfl

def actualActionStateMap (k : ℕ) (f : FieldIndex → ℝ) :
    AugmentedState k →ₗ[ℝ] AugmentedState k where
  toFun := fun S => actualAction k S f
  map_add' S T := by
    simp [actualAction, physicalAffineFieldAction, map_add, Matrix.add_mulVec, add_mul]
  map_smul' a S := by
    simp [actualAction, physicalAffineFieldAction, map_smul,
      Matrix.smul_mulVec_assoc, smul_mul_assoc]

def actualActionCoordinateStateMap (k : ℕ) (j : FieldIndex) :
    (AugmentedCoordinateIndex k → ℝ) →ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) :=
  (augmentedStateCoordinates k).toLinearMap.comp
    ((actualActionStateMap k (Pi.single j 1)).comp
      (augmentedStateCoordinates k).symm.toLinearMap)

def actualActionPolynomial (k : ℕ) (r : AugmentedCoordinateIndex k) :
    MvPolynomial (AugmentedCoordinateIndex k ⊕ FieldIndex) ℝ :=
  ∑ j : FieldIndex,
    MvPolynomial.rename Sum.inl (linearCoordinatePolynomial (actualActionCoordinateStateMap k j) r) *
      MvPolynomial.X (Sum.inr j)

theorem eval_actualActionPolynomial (k : ℕ) (S : AugmentedState k)
    (f : FieldIndex → ℝ) (r : AugmentedCoordinateIndex k) :
    MvPolynomial.eval (Sum.elim (augmentedStateCoordinates k S) f)
      (actualActionPolynomial k r) = augmentedStateCoordinates k (actualAction k S f) r := by
  let L := (augmentedStateCoordinates k).toLinearMap.comp (actualActionFieldMap k S)
  have hentry (j : FieldIndex) :
      LinearMap.toMatrix' L r j = augmentedStateCoordinates k (actualAction k S (Pi.single j 1)) r := by
    rw [LinearMap.toMatrix'_apply]
    have he : (fun i : FieldIndex => if i = j then (1 : ℝ) else 0) = Pi.single j 1 := by
      ext i
      simp [Pi.single_apply, eq_comm]
    rw [he]
    rfl
  have hL : (LinearMap.toMatrix' L *ᵥ f) r = L f r :=
    congrArg (fun g : (FieldIndex → ℝ) →ₗ[ℝ] (AugmentedCoordinateIndex k → ℝ) => g f r)
      (Matrix.toLin'_toMatrix' L)
  simp only [actualActionPolynomial, MvPolynomial.eval_sum, map_mul,
    MvPolynomial.eval_rename, MvPolynomial.eval_X]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    eval_linearCoordinatePolynomial]
  have he (j : FieldIndex) :
      actualActionCoordinateStateMap k j (augmentedStateCoordinates k S) r =
        LinearMap.toMatrix' L r j := by
    rw [hentry]
    simp [actualActionCoordinateStateMap, actualActionStateMap]
  simp only [he]
  exact hL

theorem continuous_actualAction (k : ℕ) :
    Continuous (fun z : AugmentedState k × (FieldIndex → ℝ) => actualAction k z.1 z.2) := by
  have hcoords : Continuous (fun z : AugmentedState k × (FieldIndex → ℝ) =>
      Sum.elim (augmentedStateCoordinates k z.1) z.2) := by
    apply continuous_pi
    intro a
    cases a with
    | inl r =>
      exact (continuous_apply r).comp
        ((augmentedStateCoordinates k).toLinearMap.continuous_of_finiteDimensional.comp continuous_fst)
    | inr j => exact (continuous_apply j).comp continuous_snd
  have hout : Continuous (fun z : AugmentedState k × (FieldIndex → ℝ) =>
      augmentedStateCoordinates k (actualAction k z.1 z.2)) := by
    apply continuous_pi
    intro r
    exact ((actualActionPolynomial k r).continuous_eval.comp hcoords).congr
      (fun z => eval_actualActionPolynomial k z.1 z.2 r)
  exact ((augmentedStateCoordinates k).symm.toLinearMap.continuous_of_finiteDimensional.comp hout).congr
    (fun z => (augmentedStateCoordinates k).symm_apply_apply _)

theorem continuous_fieldNorm : Continuous fieldNorm := by
  unfold fieldNorm coordinateL2Norm
  fun_prop

theorem continuous_gap (k : ℕ) :
    Continuous (fun z : AugmentedState k × (FieldIndex → ℝ) => gap k z.1 z.2) := by
  have hphase : Continuous (coefficientEuclideanNorm : CoefficientSpace k → ℝ) := by
    unfold coefficientEuclideanNorm
    fun_prop
  have hphysical : Continuous (physicalAffineNorm : PhysicalAffineData → ℝ) := by
    unfold physicalAffineNorm
    fun_prop
  have hmatrix : Continuous (fun z : AugmentedState k × (FieldIndex → ℝ) => fieldMatrix z.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply (i,j)).comp continuous_snd
  exact ((hphase.comp (continuous_fst.comp (continuous_actualAction k))).add
    (hphysical.comp (continuous_snd.comp (continuous_actualAction k)))).max
      ((continuous_descendingSingularValue (1 : Fin 4)).comp hmatrix)

end PaperI.AffineConditioning
