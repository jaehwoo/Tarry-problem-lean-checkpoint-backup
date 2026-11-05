import PaperILean.RawJetUniformBounds
import PaperILean.TranslationGramBound

/-! I255-257: retain the small physical direction |Bu| in the contraction.
The remaining frame slots use a conservative 9^k constant, independent of all
variable source parameters. Singular B and Bu=0 are allowed in these upper bounds.
-/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

theorem tensor_frame_curryLeft {n : ℕ} (T : TensorSpace (n + 1))
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    (T.compContinuousLinearMap (fun _ => frameLinearMap B)).curryLeft u =
      (T.curryLeft (B *ᵥ u)).compContinuousLinearMap (fun _ => frameLinearMap B) := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, frameLinearMap_apply]
  congr 1
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

theorem tensor_frame_contraction_bound {n : ℕ} (T : TensorSpace (n + 1))
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : euclideanFrameOperatorNorm B ≤ 1)
    (u : PhysicalSpace) :
    tensorHSNorm ((T.compContinuousLinearMap (fun _ => frameLinearMap B)).curryLeft u) ≤
      (9 : ℝ) ^ n * physicalEuclideanNorm (B *ᵥ u) * tensorHSNorm T := by
  rw [tensor_frame_curryLeft]
  have hb := (euclideanFrameOperatorNorm_le_iff B 1 zero_le_one).mp hB
  have he := frame_entry_le_of_euclidean_bound B 1 hb
  have h := tensorHSNorm_frame_bound (T.curryLeft (B *ᵥ u)) B 1 zero_le_one he
  simp only [mul_one] at h
  calc
    _ ≤ (9 : ℝ) ^ n * tensorHSNorm (T.curryLeft (B *ᵥ u)) := h
    _ ≤ (9 : ℝ) ^ n * (physicalEuclideanNorm (B *ᵥ u) * tensorHSNorm T) :=
      mul_le_mul_of_nonneg_left (tensorHSNorm_curryLeft_le T _) (by positivity)
    _ = _ := by ring

theorem source_rawJetContraction_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ B : Matrix (Fin 3) (Fin 3) ℝ, euclideanFrameOperatorNorm B ≤ 1 →
      ∀ n : ℕ, n + 1 ≤ k → ∀ u : PhysicalSpace,
        tensorHSNorm ((affineJetTensor F c B (n + 1)).curryLeft u) ≤
          C * R * physicalEuclideanNorm (B *ᵥ u) := by
  obtain ⟨A, hA, ha⟩ := rawJetHSNorm_uniform_bound k X hX
  refine ⟨2 * (9 : ℝ) ^ k * A, by positivity, ?_⟩
  intro R hR F hF c hc B hB n hn u
  have hU := physicalEuclideanNorm_nonneg (B *ᵥ u)
  have hraw : tensorHSNorm (iteratedFDeriv ℝ (n + 1) (phase F) c) ≤ A * (2 * R) :=
    (ha F c hc (n + 1) hn).trans (mul_le_mul_of_nonneg_left hF (by linarith))
  have hpow : (9 : ℝ) ^ n ≤ (9 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (9 : ℝ) ^ n * physicalEuclideanNorm (B *ᵥ u) *
        tensorHSNorm (iteratedFDeriv ℝ (n + 1) (phase F) c) :=
      tensor_frame_contraction_bound _ B hB u
    _ ≤ (9 : ℝ) ^ n * physicalEuclideanNorm (B *ᵥ u) * (A * (2 * R)) :=
      mul_le_mul_of_nonneg_left hraw (mul_nonneg (by positivity) hU)
    _ ≤ (9 : ℝ) ^ k * physicalEuclideanNorm (B *ᵥ u) * (A * (2 * R)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hU) (by positivity)
    _ = _ := by ring

theorem source_directionalContraction_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ B : Matrix (Fin 3) (Fin 3) ℝ, euclideanFrameOperatorNorm B ≤ 1 →
      ∀ n : ℕ, n + 2 ≤ k → ∀ u : PhysicalSpace,
        directionalContractionHSNorm F c B u n ≤ C * R * physicalEuclideanNorm (B *ᵥ u) := by
  obtain ⟨C, hC, hb⟩ := source_rawJetContraction_uniform_bound k X hX
  refine ⟨C, hC, ?_⟩
  intro R hR F hF c hc B hB n hn u
  exact hb R hR F hF c hc B hB (n + 1) hn u

theorem source_weightedContraction_uniform_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ B : Matrix (Fin 3) (Fin 3) ℝ, euclideanFrameOperatorNorm B ≤ 1 →
      ∀ u : PhysicalSpace, translationWeightedContractionSum F c B u ≤
        C * R ^ 2 * (physicalEuclideanNorm (B *ᵥ u)) ^ 2 := by
  obtain ⟨A, hA, ha⟩ := source_directionalContraction_uniform_bound k X hX
  refine ⟨(∑ n ∈ Finset.range (k - 1), (n + 2 : ℝ)) * A ^ 2, by positivity, ?_⟩
  intro R hR F hF c hc B hB u
  unfold translationWeightedContractionSum
  calc
    _ ≤ ∑ n ∈ Finset.range (k - 1), (n + 2 : ℝ) *
        (A * R * physicalEuclideanNorm (B *ᵥ u)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hr : n + 2 ≤ k := by have := Finset.mem_range.mp hn; omega
      have h := ha R hR F hF c hc B hB n hr u
      have h0 : 0 ≤ directionalContractionHSNorm F c B u n := tensorHSNorm_nonneg _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end PaperI
