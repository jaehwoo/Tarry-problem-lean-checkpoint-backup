import PaperILean.AugmentedOrbit

/-! The exact normal three-column restriction, in manuscript order A,C,Tx.
The scalar affine multiplier is applied to the full derivative before its
constant is discarded. All physical affine coefficients are retained. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def normalCoordinates : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun v := ![v 0, v 1, v 2, 0, 0, 0]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' r v := by ext i; fin_cases i <;> simp

theorem normalCoordinates_injective : Function.Injective normalCoordinates := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

def normalScalarPolynomial (v : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (v 2) + MvPolynomial.C (v 0) * MvPolynomial.X 1 +
    MvPolynomial.C (v 1) * MvPolynomial.X 2

theorem eval_normalScalarPolynomial (v : Fin 3 → ℝ) (x : PhysicalSpace) :
    MvPolynomial.eval x (normalScalarPolynomial v) = v 2 + v 0 * x 1 + v 1 * x 2 := by
  simp [normalScalarPolynomial]

theorem normalScalarPolynomial_zero : normalScalarPolynomial 0 = 0 := by
  simp [normalScalarPolynomial]

theorem normalScalarPolynomial_eq_zero_iff (v : Fin 3 → ℝ) :
    normalScalarPolynomial v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 := congrArg (MvPolynomial.eval (0 : PhysicalSpace)) h
    have h0 := congrArg (MvPolynomial.eval ![(0 : ℝ), 1, 0]) h
    have h1 := congrArg (MvPolynomial.eval ![(0 : ℝ), 0, 1]) h
    simp only [eval_normalScalarPolynomial, map_zero] at h0 h1 h2
    simp only [Pi.zero_apply, mul_zero, add_zero] at h2
    simp [h2] at h0 h1
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    exact normalScalarPolynomial_zero

theorem upperAffineFieldTranslation_normalCoordinates (v : Fin 3 → ℝ) :
    upperAffineFieldTranslation (normalCoordinates v) = ![v 2, 0, 0] := rfl

theorem upperAffineFieldLinear_normalCoordinates (v : Fin 3 → ℝ) :
    upperAffineFieldLinear (normalCoordinates v) = !![0, v 0, v 1; 0, 0, 0; 0, 0, 0] := rfl

theorem affineFieldPolynomialMap_normal (v : Fin 3 → ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    affineFieldPolynomialMap (upperAffineFieldTranslation (normalCoordinates v))
      (upperAffineFieldLinear (normalCoordinates v)) F =
        normalScalarPolynomial v * MvPolynomial.pderiv 0 F := by
  simp [affineFieldPolynomialMap_apply, upperAffineFieldTranslation_normalCoordinates,
    upperAffineFieldLinear_normalCoordinates, affineCoordinate, Fin.sum_univ_succ,
    normalScalarPolynomial, add_assoc]

def normalOrbitDifferential (k : ℕ) (S : AugmentedState k) :
    (Fin 3 → ℝ) →ₗ[ℝ] AugmentedState k :=
  (augmentedOrbitDifferential k S).comp normalCoordinates

theorem normalOrbitDifferential_apply {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) :
    normalOrbitDifferential k S v = augmentedOrbitDifferential k S (normalCoordinates v) := rfl

theorem polynomial_normalOrbit_phase {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) :
    coefficientPolynomial (normalOrbitDifferential k S v).1 =
      normalScalarPolynomial v * MvPolynomial.pderiv 0 (coefficientPolynomial S.1) -
        MvPolynomial.C (MvPolynomial.coeff 0
          (normalScalarPolynomial v * MvPolynomial.pderiv 0 (coefficientPolynomial S.1))) := by
  change coefficientPolynomial (affineFieldCoefficientMap k _ _ S.1) = _
  rw [polynomial_affineFieldCoefficientMap, affineFieldPolynomialMap_normal]

theorem normalOrbit_phase_zero_implies_product_constant {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) (hz : (normalOrbitDifferential k S v).1 = 0) :
    normalScalarPolynomial v * MvPolynomial.pderiv 0 (coefficientPolynomial S.1) =
      MvPolynomial.C (MvPolynomial.coeff 0
        (normalScalarPolynomial v * MvPolynomial.pderiv 0 (coefficientPolynomial S.1))) := by
  have h := polynomial_normalOrbit_phase S v
  rw [hz] at h
  have hzero : coefficientPolynomial (0 : CoefficientSpace k) = 0 := by
    simp [coefficientPolynomial]
  rw [hzero] at h
  exact sub_eq_zero.mp h.symm

theorem normalOrbit_physical_translation {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) (i : Fin 3) :
    (normalOrbitDifferential k S v).2.1 i = S.2.2 i 0 * v 2 := by
  simp [normalOrbitDifferential, augmentedOrbitDifferential, physicalAffineFieldAction,
    upperAffineFieldTranslation_normalCoordinates, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

theorem normalOrbit_physical_linear {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) (i j : Fin 3) :
    (normalOrbitDifferential k S v).2.2 i j = S.2.2 i 0 * ![0, v 0, v 1] j := by
  fin_cases j <;> simp [normalOrbitDifferential, augmentedOrbitDifferential,
    physicalAffineFieldAction, upperAffineFieldLinear_normalCoordinates,
    Matrix.mul_apply, Fin.sum_univ_succ]

theorem normalOrbit_physical_zero_implies_eq_zero {k : ℕ} (S : AugmentedState k)
    (hM : (fun i => S.2.2 i 0) ≠ 0) (v : Fin 3 → ℝ)
    (hz : (normalOrbitDifferential k S v).2 = 0) : v = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, S.2.2 i 0 ≠ 0 := by
    by_contra! h
    exact hM (funext h)
  have ht := congrArg (fun ell : PhysicalAffineData => ell.1 i) hz
  have h0 := congrArg (fun ell : PhysicalAffineData => ell.2 i 1) hz
  have h1 := congrArg (fun ell : PhysicalAffineData => ell.2 i 2) hz
  simp only [normalOrbit_physical_translation, Prod.fst_zero, Pi.zero_apply] at ht
  simp only [normalOrbit_physical_linear, Prod.snd_zero, Pi.zero_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two] at h0 h1
  have hv2 := (mul_eq_zero.mp ht).resolve_left hi
  have hv0 := (mul_eq_zero.mp h0).resolve_left hi
  have hv1 := (mul_eq_zero.mp h1).resolve_left hi
  funext j
  fin_cases j <;> assumption

end PaperI
