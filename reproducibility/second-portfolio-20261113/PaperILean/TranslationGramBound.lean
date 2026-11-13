import PaperILean.PolynomialDerivativeVanishing
import PaperILean.TranslationStopStability

/-! The source Gram dominance implies the actual augmented coefficient bound.
Every parent grade r=2,...,k is retained. For convenient dependent tensor types
the contraction indexed by n has parent order n+2; the exact Icc reindexing is
proved below. The Gram input is explicit, and is not a theorem about a
minimizing frame. Constants are chosen before phase, center, frame and direction.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

def directionalContractionHSNorm {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (u : PhysicalSpace) (n : ℕ) : ℝ :=
  tensorHSNorm ((affineJetTensor F c B (n + 2)).curryLeft u)

def translationWeightedContractionSum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) : ℝ :=
  ∑ n ∈ Finset.range (k - 1), (n + 2 : ℝ) * (directionalContractionHSNorm F c B u n) ^ 2

theorem sum_range_pred_eq_sum_Icc (k : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range (k - 1), f n = ∑ r ∈ Finset.Icc 2 k, f (r - 2) := by
  apply Finset.sum_bij (fun n _ => n + 2)
  · intro n hn
    have h := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn m hm h
    omega
  · intro r hr
    have h := Finset.mem_Icc.mp hr
    refine ⟨r - 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    simp

theorem translationWeightedContractionSum_eq_Icc {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    translationWeightedContractionSum F c B u =
      ∑ r ∈ Finset.Icc 2 k, (r : ℝ) *
        (directionalContractionHSNorm F c B u (r - 2)) ^ 2 := by
  unfold translationWeightedContractionSum
  rw [sum_range_pred_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro r hr
  have h := Finset.mem_Icc.mp hr
  have he : r - 2 + 2 = r := by omega
  rw [show (r - 2 : ℕ) + (2 : ℝ) = (r : ℝ) by exact_mod_cast he]

theorem jetTensorHSNorm_origin_eq_tensorHSNorm {k : ℕ} (F : CoefficientSpace k)
    (n : ℕ) : jetTensorHSNorm F 0 1 n = tensorHSNorm (iteratedFDeriv ℝ n (phase F) 0) := by
  rw [← tensorHSNorm_affineJetTensor, affineJetTensor_at_origin_identity]

theorem affine_directional_jetHSNorm {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) (n : ℕ) :
    jetTensorHSNorm (directionalCoefficientMap k u (affineCoefficientMap k c B F))
      0 1 (n + 1) = directionalContractionHSNorm F c B u n := by
  rw [jetTensorHSNorm_origin_eq_tensorHSNorm, iteratedFDeriv_affine_directional_positive]
  rfl

theorem completeJetHSNorm_nonneg {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ completeJetHSNorm F c B :=
  Real.sqrt_nonneg _

theorem completeJetHSNorm_sq {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (completeJetHSNorm F c B) ^ 2 =
      ∑ n ∈ Finset.range k, (jetTensorHSNorm F c B (n + 1)) ^ 2 := by
  unfold completeJetHSNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact (Finset.sum_range (fun n => (jetTensorHSNorm F c B (n + 1)) ^ 2)).symm

theorem affine_directional_completeJetHSNorm_sq {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    (completeJetHSNorm
      (directionalCoefficientMap k u (affineCoefficientMap k c B F)) 0 1) ^ 2 =
      ∑ n ∈ Finset.range (k - 1), (directionalContractionHSNorm F c B u n) ^ 2 := by
  rw [completeJetHSNorm_sq]
  cases k with
  | zero => simp
  | succ k =>
    have ht : jetTensorHSNorm
        (directionalCoefficientMap (k + 1) u (affineCoefficientMap (k + 1) c B F))
          0 1 (k + 1) = 0 := by
      rw [jetTensorHSNorm_origin_eq_tensorHSNorm,
        iteratedFDeriv_affine_directional_top_eq_zero, tensorHSNorm_zero]
    rw [Finset.sum_range_succ, ht]
    simp only [zero_pow (by decide : 2 ≠ 0), add_zero, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro n hn
    rw [affine_directional_jetHSNorm]

theorem translationWeightedContractionSum_le_completeHS {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (u : PhysicalSpace) :
    translationWeightedContractionSum F c B u ≤ (k : ℝ) *
      (completeJetHSNorm
        (directionalCoefficientMap k u (affineCoefficientMap k c B F)) 0 1) ^ 2 := by
  rw [affine_directional_completeJetHSNorm_sq]
  unfold translationWeightedContractionSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := Finset.mem_range.mp hn
  have hk : n + 2 ≤ k := by omega
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast hk

theorem translationWeightedContractionSum_le_coefficient {k : ℕ}
    (C : ℝ) (hC : 1 ≤ C)
    (heq : ∀ G : CoefficientSpace k, completeJetHSNorm G 0 1 ≤ C * coefficientEuclideanNorm G)
    (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (u : PhysicalSpace) :
    translationWeightedContractionSum F c B u ≤ (k : ℝ) * C ^ 2 *
      (coefficientEuclideanNorm
        (directionalCoefficientMap k u (affineCoefficientMap k c B F))) ^ 2 := by
  let G := directionalCoefficientMap k u (affineCoefficientMap k c B F)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hnorm := heq G
  have hs : (completeJetHSNorm G 0 1) ^ 2 ≤ C ^ 2 * (coefficientEuclideanNorm G) ^ 2 := by
    have hp := mul_le_mul hnorm hnorm (completeJetHSNorm_nonneg G 0 1)
      (mul_nonneg hC0 (coefficientEuclideanNorm_nonneg G))
    nlinarith only [hp]
  exact (translationWeightedContractionSum_le_completeHS F c B u).trans
    ((mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)).trans_eq (by dsimp [G]; ring))

theorem augmentedTranslation_lower_bound_of_gram_dominance (k : ℕ) (_hk : 2 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace)
      (B : Matrix (Fin 3) (Fin 3) ℝ),
      (∀ u : PhysicalSpace, (physicalEuclideanNorm u) ^ 2 ≤
        (physicalEuclideanNorm (B *ᵥ u)) ^ 2 + translationWeightedContractionSum F c B u) →
      ∀ u : PhysicalSpace, b * (physicalEuclideanNorm u) ^ 2 ≤
        augmentedTranslationQuadratic F c B u := by
  obtain ⟨C, hC, heq⟩ := completeJet_norm_equivalence k
  let K : ℝ := (k : ℝ) * C ^ 2
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)
  have hD : 0 < 1 + K := by positivity
  refine ⟨(1 + K)⁻¹, inv_pos.mpr hD, ?_⟩
  intro F c B hgram u
  have hw := translationWeightedContractionSum_le_coefficient C hC
    (fun G => (heq G).2) F c B u
  have hg := hgram u
  rw [inv_mul_le_iff₀ hD]
  unfold augmentedTranslationQuadratic
  dsimp [K] at *
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg C))
    (sq_nonneg (physicalEuclideanNorm (B *ᵥ u)))]

theorem augmentedTranslation_uniform_radius_of_gram_dominance (k : ℕ) (hk : 2 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ),
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
      (∀ u : PhysicalSpace, (physicalEuclideanNorm u) ^ 2 ≤
        (physicalEuclideanNorm (B *ᵥ u)) ^ 2 + translationWeightedContractionSum F c B u) →
      ∀ h : PhysicalSpace, physicalEuclideanNorm h ≤ δ → ∀ u : PhysicalSpace,
        (b / 2) * (physicalEuclideanNorm u) ^ 2 ≤
          augmentedTranslationQuadratic F (c + B *ᵥ h) B u := by
  obtain ⟨b, hb, hlo⟩ := augmentedTranslation_lower_bound_of_gram_dominance k hk
  refine ⟨b, hb, ?_⟩
  intro M
  obtain ⟨δ, hd, hd1, hδ⟩ := translationStop_uniform_radius k M b hb
  refine ⟨δ, hd, hd1, ?_⟩
  intro F c B hM hg h hh u
  exact hδ F c B hM (hlo F c B hg) h hh u

end PaperI
