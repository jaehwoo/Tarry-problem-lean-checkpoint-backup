import PaperILean.TensorContractionBounds
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Euclidean operator bounds and full ordered-component HS frame pullback.
Every tensor slot is transformed. The conservative constant (9L)^n depends
only on the displayed entry bound and tensor order. No invertibility is needed
for this upper estimate, and order zero is included. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def euclideanFrameMap (A : Matrix (Fin 3) (Fin 3) ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ PhysicalSpace).symm.toLinearMap.comp
      ((frameLinearMap A).toLinearMap.comp
        (WithLp.linearEquiv 2 ℝ PhysicalSpace).toLinearMap))

theorem euclideanFrameMap_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (v : PhysicalSpace) :
    euclideanFrameMap A ((WithLp.linearEquiv 2 ℝ PhysicalSpace).symm v) =
      (WithLp.linearEquiv 2 ℝ PhysicalSpace).symm (A *ᵥ v) := by
  change (WithLp.linearEquiv 2 ℝ PhysicalSpace).symm (frameLinearMap A v) = _
  rw [frameLinearMap_apply]

def euclideanFrameOperatorNorm (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ‖euclideanFrameMap A‖

theorem euclideanFrameOperatorNorm_le_iff (A : Matrix (Fin 3) (Fin 3) ℝ)
    (L : ℝ) (hL : 0 ≤ L) :
    euclideanFrameOperatorNorm A ≤ L ↔
      ∀ v : PhysicalSpace, physicalEuclideanNorm (A *ᵥ v) ≤ L * physicalEuclideanNorm v := by
  constructor
  · intro h v
    simp only [physicalEuclideanNorm, coordinateL2Norm_eq_norm]
    rw [← euclideanFrameMap_apply]
    exact ((euclideanFrameMap A).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    apply (euclideanFrameMap A).opNorm_le_bound hL
    intro x
    have hv := h ((WithLp.linearEquiv 2 ℝ PhysicalSpace) x)
    simp only [physicalEuclideanNorm, coordinateL2Norm_eq_norm] at hv
    rw [← euclideanFrameMap_apply, LinearEquiv.symm_apply_apply] at hv
    exact hv

theorem physicalEuclideanNorm_single (j : Fin 3) :
    physicalEuclideanNorm (Pi.single j (1 : ℝ)) = 1 := by
  simp [physicalEuclideanNorm, coordinateL2Norm, Pi.single_apply]

theorem frame_entry_le_of_euclidean_bound (A : Matrix (Fin 3) (Fin 3) ℝ)
    (L : ℝ) (h : ∀ v : PhysicalSpace,
      physicalEuclideanNorm (A *ᵥ v) ≤ L * physicalEuclideanNorm v) (i j : Fin 3) :
    |A i j| ≤ L := by
  have hi := abs_le_sqrt_sum_sq (A *ᵥ Pi.single j (1 : ℝ)) i
  have hb := h (Pi.single j (1 : ℝ))
  rw [physicalEuclideanNorm_single, mul_one] at hb
  have he : |A i j| ≤ physicalEuclideanNorm (A *ᵥ Pi.single j (1 : ℝ)) := by
    simpa [Matrix.mulVec_single_one, physicalEuclideanNorm, coordinateL2Norm] using hi
  exact he.trans hb

theorem coordinateL2Norm_le_of_component_bound {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (h : ∀ i, |v i| ≤ M) :
    coordinateL2Norm v ≤ Real.sqrt (Fintype.card ι : ℝ) * M := by
  classical
  have hs : ∑ i, (v i) ^ 2 ≤ ∑ _i : ι, M ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hp := mul_le_mul (h i) (h i) (abs_nonneg (v i)) hM
    simpa only [← pow_two, sq_abs] using hp
  unfold coordinateL2Norm
  apply (Real.sqrt_le_sqrt hs).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

theorem abs_tensorCoordinates_le_HS {n : ℕ} (T : TensorSpace n) (a : Fin n → Fin 3) :
    |tensorCoordinates T a| ≤ tensorHSNorm T :=
  abs_le_sqrt_sum_sq (tensorCoordinates T) a

theorem tensor_frame_component_bound {n : ℕ} (T : TensorSpace n)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ i j, |A i j| ≤ L) (b : Fin n → Fin 3) :
    |tensorCoordinates (T.compContinuousLinearMap (fun _ => frameLinearMap A)) b| ≤
      (3 * L) ^ n * tensorHSNorm T := by
  classical
  unfold tensorCoordinates
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, frameLinearMap_apply]
  rw [tensor_expand_coordinates]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ a : Fin n → Fin 3,
      |(∏ j, (A *ᵥ Pi.single (b j) (1 : ℝ)) (a j)) *
        T (fun j => Pi.single (a j) (1 : ℝ))|) ≤
        ∑ _a : Fin n → Fin 3, L ^ n * tensorHSNorm T := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      have hp : |∏ j : Fin n, (A *ᵥ Pi.single (b j) (1 : ℝ)) (a j)| ≤ L ^ n := by
        rw [Finset.abs_prod]
        have hprod := Finset.prod_le_prod (s := Finset.univ) (fun j _ => abs_nonneg
          ((A *ᵥ Pi.single (b j) (1 : ℝ)) (a j)))
          (fun j _ => by simpa [Matrix.mulVec_single_one] using hA (a j) (b j))
        simpa using hprod
      exact mul_le_mul hp (abs_tensorCoordinates_le_HS T a)
        (abs_nonneg _) (pow_nonneg hL _)
    _ = (3 * L) ^ n * tensorHSNorm T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_pow]
      ring

theorem sqrt_three_pow_le (n : ℕ) : Real.sqrt ((3 : ℝ) ^ n) ≤ (3 : ℝ) ^ n := by
  have h : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith⟩

theorem tensorHSNorm_frame_bound {n : ℕ} (T : TensorSpace n)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ i j, |A i j| ≤ L) :
    tensorHSNorm (T.compContinuousLinearMap (fun _ => frameLinearMap A)) ≤
      (9 * L) ^ n * tensorHSNorm T := by
  have hb := coordinateL2Norm_le_of_component_bound
    (tensorCoordinates (T.compContinuousLinearMap (fun _ => frameLinearMap A)))
    ((3 * L) ^ n * tensorHSNorm T)
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hL) _) (tensorHSNorm_nonneg T))
    (tensor_frame_component_bound T A L hL hA)
  have hcard : (Fintype.card (Fin n → Fin 3) : ℝ) = (3 : ℝ) ^ n := by simp
  rw [hcard] at hb
  apply hb.trans
  calc
    Real.sqrt ((3 : ℝ) ^ n) * ((3 * L) ^ n * tensorHSNorm T) ≤
      (3 : ℝ) ^ n * ((3 * L) ^ n * tensorHSNorm T) :=
      mul_le_mul_of_nonneg_right (sqrt_three_pow_le n)
        (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hL) _) (tensorHSNorm_nonneg T))
    _ = ((3 : ℝ) ^ n * (3 * L) ^ n) * tensorHSNorm T := by ring
    _ = (3 * (3 * L)) ^ n * tensorHSNorm T := by rw [← mul_pow]
    _ = (9 * L) ^ n * tensorHSNorm T := by congr 2; ring

end PaperI
