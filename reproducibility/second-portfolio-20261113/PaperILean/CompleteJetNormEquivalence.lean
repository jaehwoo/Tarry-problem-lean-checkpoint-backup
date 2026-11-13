import PaperILean.CompleteSymmetricJetEquiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Two-sided Euclidean coefficient / ordered-component Hilbert--Schmidt bounds.
Constants are chosen for each k before the phase and before any affine frame.
Pi operator norms are used only inside a proved finite-dimensional bridge.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

abbrev OriginTensorComponentIndex (k : ℕ) := Σ r : Fin k, Fin (r.val + 1) → Fin 3

def originTensorComponents (k : ℕ) :
    CoefficientSpace k →ₗ[ℝ] (OriginTensorComponentIndex k → ℝ) where
  toFun F w := (completeJetSymmetricMap k F w.1).val
    (fun j => Pi.single (w.2 j) (1 : ℝ))
  map_add' F G := by
    funext w
    simp [map_add, ContinuousMultilinearMap.add_apply]
  map_smul' a F := by
    funext w
    simp [map_smul, ContinuousMultilinearMap.smul_apply]

theorem originTensorComponents_injective (k : ℕ) :
    Function.Injective (originTensorComponents k) := by
  intro F G h
  apply (completeJetSymmetricEquiv k).injective
  funext r
  apply Subtype.ext
  apply tensor_eq_of_coordinates
  intro a
  exact congrFun h ⟨r, a⟩

def coefficientEuclideanNorm {k : ℕ} (F : CoefficientSpace k) : ℝ :=
  Real.sqrt (∑ α, (F α) ^ 2)

def completeJetHSNorm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (∑ r : Fin k, (jetTensorHSNorm F c B (r.val + 1)) ^ 2)

def originTensorEuclideanMap (k : ℕ) :
    EuclideanSpace ℝ (MonomialIndex k) →ₗ[ℝ]
      EuclideanSpace ℝ (OriginTensorComponentIndex k) :=
  (WithLp.linearEquiv 2 ℝ (OriginTensorComponentIndex k → ℝ)).symm.toLinearMap.comp
    ((originTensorComponents k).comp
      (WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).toLinearMap)

theorem originTensorEuclideanMap_injective (k : ℕ) :
    Function.Injective (originTensorEuclideanMap k) :=
  (WithLp.linearEquiv 2 ℝ (OriginTensorComponentIndex k → ℝ)).symm.injective.comp
    ((originTensorComponents_injective k).comp
      (WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).injective)

theorem coefficientEuclideanNorm_eq_norm {k : ℕ} (F : CoefficientSpace k) :
    coefficientEuclideanNorm F =
      ‖(WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm F‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [coefficientEuclideanNorm, Real.norm_eq_abs, sq_abs]

theorem completeJetHSNorm_eq_norm {k : ℕ} (F : CoefficientSpace k) :
    completeJetHSNorm F 0 1 =
      ‖originTensorEuclideanMap k ((WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm F)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold completeJetHSNorm jetTensorHSNorm
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [jetTensorComponent, Matrix.one_mulVec]
  simp [originTensorEuclideanMap, originTensorComponents, completeJetSymmetricMap,
    Real.norm_eq_abs, sq_abs]

theorem completeJet_norm_equivalence (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ F : CoefficientSpace k,
      C⁻¹ * coefficientEuclideanNorm F ≤ completeJetHSNorm F 0 1 ∧
      completeJetHSNorm F 0 1 ≤ C * coefficientEuclideanNorm F := by
  let L := originTensorEuclideanMap k
  let A := LinearMap.toContinuousLinearMap L
  obtain ⟨K, _, hK⟩ := L.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (originTensorEuclideanMap_injective k))
  let C : ℝ := max 1 (max (K : ℝ) ‖A‖)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hKC : (K : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hAC : ‖A‖ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro F
  rw [coefficientEuclideanNorm_eq_norm, completeJetHSNorm_eq_norm]
  let x := (WithLp.linearEquiv 2 ℝ (CoefficientSpace k)).symm F
  have hlo : ‖x‖ ≤ (K : ℝ) * ‖L x‖ := by
    simpa using hK.le_mul_dist x 0
  have hhi : ‖L x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  constructor
  · rw [inv_mul_le_iff₀ hC0]
    exact hlo.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _))
  · exact hhi.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg _))

theorem completeJetHSNorm_affine (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    completeJetHSNorm (affineCoefficientMap k c B F) 0 1 = completeJetHSNorm F c B := by
  unfold completeJetHSNorm jetTensorHSNorm jetTensorComponent
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.one_mulVec]
  rw [iteratedFDeriv_phase_affine_zero_positive]

theorem affine_completeJet_norm_equivalence (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
      (B : Matrix (Fin 3) (Fin 3) ℝ),
      C⁻¹ * coefficientEuclideanNorm (affineCoefficientMap k c B F) ≤
        completeJetHSNorm F c B ∧
      completeJetHSNorm F c B ≤
        C * coefficientEuclideanNorm (affineCoefficientMap k c B F) := by
  obtain ⟨C, hC, h⟩ := completeJet_norm_equivalence k
  refine ⟨C, hC, ?_⟩
  intro F c B
  simpa only [completeJetHSNorm_affine] using h (affineCoefficientMap k c B F)

end PaperI
