import PaperILean.TensorFrameBounds
import PaperILean.TranslationGramBound

/-! Uniform centered coefficient pullback and exact directional covariance.
The full nonconstant coefficient class and every positive jet grade are used.
The inverse recovery is proved only under the displayed nonsingularity input.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem fderiv_phase_centered_affine {k : ℕ} (F : CoefficientSpace k)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x u : PhysicalSpace) :
    fderiv ℝ (phase (affineCoefficientMap k 0 A F)) x u =
      fderiv ℝ (phase F) (A *ᵥ x) (A *ᵥ u) := by
  rw [fderiv_phase_affine_apply,
    (hasFDerivAt_phase F (A *ᵥ x)).fderiv]
  simp [affinePoint_eq_frame, polynomialDifferential_apply, frameLinearMap_apply]

theorem directionalCoefficient_centered_covariance {k : ℕ} (F : CoefficientSpace k)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    directionalCoefficientMap k u (affineCoefficientMap k 0 A F) =
      affineCoefficientMap k 0 A (directionalCoefficientMap k (A *ᵥ u) F) := by
  apply coefficient_ext
  intro x
  rw [phase_directionalCoefficientMap, phase_affineCoefficientMap,
    phase_directionalCoefficientMap, phase_directionalCoefficientMap,
    fderiv_phase_centered_affine, fderiv_phase_centered_affine]
  simp [affinePoint_eq_frame, frameLinearMap_apply]

theorem directionalCoefficient_right_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    directionalCoefficientMap k u (affineCoefficientMap k c (B * A) F) =
      affineCoefficientMap k 0 A
        (directionalCoefficientMap k (A *ᵥ u) (affineCoefficientMap k c B F)) := by
  have hc := affineCoefficientMap_comp k c 0 B A F
  simp only [Matrix.mulVec_zero, add_zero] at hc
  rw [← hc, directionalCoefficient_centered_covariance]

theorem directionalCoefficient_right_frame_inverse {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0)
    (u : PhysicalSpace) :
    affineCoefficientMap k 0 A⁻¹
      (directionalCoefficientMap k u (affineCoefficientMap k c (B * A) F)) =
      directionalCoefficientMap k (A *ᵥ u) (affineCoefficientMap k c B F) := by
  rw [directionalCoefficient_right_frame]
  simpa using affineCoefficientMap_inverse_left k 0 A hA
    (directionalCoefficientMap k (A *ᵥ u) (affineCoefficientMap k c B F))

theorem affineJetTensor_right_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) :
    affineJetTensor F c (B * A) n =
      (affineJetTensor F c B n).compContinuousLinearMap (fun _ => frameLinearMap A) := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp [affineJetTensor_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    frameLinearMap_apply, Matrix.mulVec_mulVec]

theorem affineJetTensor_curry_right_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (u : PhysicalSpace) :
    (affineJetTensor F c (B * A) (n + 1)).curryLeft u =
      ((affineJetTensor F c B (n + 1)).curryLeft (A *ᵥ u)).compContinuousLinearMap
        (fun _ => frameLinearMap A) := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.curryLeft_apply, affineJetTensor_apply, frameLinearMap_apply,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  refine Fin.cases ?_ (fun l => ?_) j <;> rfl

theorem jetTensorHSNorm_centered_frame_bound {k : ℕ} (F : CoefficientSpace k)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ i j, |A i j| ≤ L) (n : ℕ) :
    jetTensorHSNorm (affineCoefficientMap k 0 A F) 0 1 (n + 1) ≤
      (9 * L) ^ (n + 1) * jetTensorHSNorm F 0 1 (n + 1) := by
  rw [jetTensorHSNorm_origin_eq_tensorHSNorm, iteratedFDeriv_phase_affine_positive,
    affinePoint_zero, jetTensorHSNorm_origin_eq_tensorHSNorm]
  exact tensorHSNorm_frame_bound _ A L hL hA

theorem completeJetHSNorm_centered_frame_bound {k : ℕ} (F : CoefficientSpace k)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hA : ∀ i j, |A i j| ≤ L) :
    completeJetHSNorm (affineCoefficientMap k 0 A F) 0 1 ≤
      (9 * L) ^ k * completeJetHSNorm F 0 1 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hbase : 1 ≤ 9 * L := by linarith
  have hp0 : 0 ≤ (9 * L) ^ k := pow_nonneg (by linarith) _
  have hs : (completeJetHSNorm (affineCoefficientMap k 0 A F) 0 1) ^ 2 ≤
      ((9 * L) ^ k) ^ 2 * (completeJetHSNorm F 0 1) ^ 2 := by
    rw [completeJetHSNorm_sq, completeJetHSNorm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnk : n + 1 ≤ k := by have := Finset.mem_range.mp hn; omega
    have hb := (jetTensorHSNorm_centered_frame_bound F A L hL0 hA n).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hnk)
        (jetTensorHSNorm_nonneg F 0 1 (n + 1)))
    have hsq := (sq_le_sq₀
      (jetTensorHSNorm_nonneg (affineCoefficientMap k 0 A F) 0 1 (n + 1))
      (mul_nonneg hp0 (jetTensorHSNorm_nonneg F 0 1 (n + 1)))).mpr hb
    simpa only [mul_pow] using hsq
  apply (sq_le_sq₀ (completeJetHSNorm_nonneg _ 0 1)
    (mul_nonneg hp0 (completeJetHSNorm_nonneg F 0 1))).mp
  simpa only [mul_pow] using hs

theorem coefficientEuclideanNorm_centered_frame_bound {k : ℕ}
    (C : ℝ) (hC : 1 ≤ C)
    (heq : ∀ G : CoefficientSpace k,
      C⁻¹ * coefficientEuclideanNorm G ≤ completeJetHSNorm G 0 1 ∧
      completeJetHSNorm G 0 1 ≤ C * coefficientEuclideanNorm G)
    (F : CoefficientSpace k) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (L : ℝ) (hL : 1 ≤ L) (hA : ∀ i j, |A i j| ≤ L) :
    coefficientEuclideanNorm (affineCoefficientMap k 0 A F) ≤
      C ^ 2 * (9 * L) ^ k * coefficientEuclideanNorm F := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlo := (inv_mul_le_iff₀ hCp).mp (heq (affineCoefficientMap k 0 A F)).1
  have hframe := completeJetHSNorm_centered_frame_bound F A L hL hA
  calc
    coefficientEuclideanNorm (affineCoefficientMap k 0 A F) ≤
      C * completeJetHSNorm (affineCoefficientMap k 0 A F) 0 1 := hlo
    _ ≤ C * ((9 * L) ^ k * completeJetHSNorm F 0 1) :=
      mul_le_mul_of_nonneg_left hframe hC0
    _ ≤ C * ((9 * L) ^ k * (C * coefficientEuclideanNorm F)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (heq F).2 (pow_nonneg (by linarith) _)) hC0
    _ = _ := by ring

theorem bounded_centeredCoefficient_pullback (k : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k),
      (∀ v : PhysicalSpace, physicalEuclideanNorm (A *ᵥ v) ≤ L * physicalEuclideanNorm v) →
      coefficientEuclideanNorm (affineCoefficientMap k 0 A F) ≤ K * coefficientEuclideanNorm F := by
  obtain ⟨C, hC, heq⟩ := completeJet_norm_equivalence k
  have hbase : 1 ≤ 9 * L := by linarith
  refine ⟨C ^ 2 * (9 * L) ^ k,
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hbase), ?_⟩
  intro A F hA
  exact coefficientEuclideanNorm_centered_frame_bound C hC heq F A L hL
    (frame_entry_le_of_euclidean_bound A L hA)

theorem boundedJet_window_right_frame {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B A : Matrix (Fin 3) (Fin 3) ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hA : ∀ v : PhysicalSpace, physicalEuclideanNorm (A *ᵥ v) ≤ L * physicalEuclideanNorm v)
    (M : ℝ) (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) :
    ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c (B * A) r ≤ (9 * L) ^ k * M := by
  have hbase : 1 ≤ 9 * L := by linarith
  have hp0 : 0 ≤ (9 * L) ^ k := pow_nonneg (by linarith) _
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 k, (9 * L) ^ k * jetTensorHSNorm F c B r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrk := (Finset.mem_Icc.mp hr).2
      rw [← tensorHSNorm_affineJetTensor, affineJetTensor_right_frame]
      have hb := tensorHSNorm_frame_bound (affineJetTensor F c B r) A L
        (zero_le_one.trans hL) (frame_entry_le_of_euclidean_bound A L hA)
      rw [tensorHSNorm_affineJetTensor] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hrk)
        (jetTensorHSNorm_nonneg F c B r))
    _ = (9 * L) ^ k * ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hM hp0

end PaperI
