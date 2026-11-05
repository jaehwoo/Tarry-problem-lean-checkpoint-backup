import PaperILean.SpectralLogBounds

/-! I259: source-uniform logarithm and complete higher-jet window at actual
minima. Constants precede R,F,c,B. The exact regularization, every tensor grade,
raw derivatives and ordered HS norm are retained throughout the trace argument.
-/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem minimizing_log_eigenvalues_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX : ℝ) (hCX : 2 ≤ CX) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ i : Fin 3, |Real.log ((frame_rightGram_posDef B).isHermitian.eigenvalues i)| ≤
        C * sourceLogScale CX R := by
  obtain ⟨a, ha, hframe⟩ := minimizing_frame_lower_bound k X hX
  obtain ⟨C, hC, hscalar⟩ := scalar_log_bound_of_inverse_radius_interval a CX ha hCX
  refine ⟨C, hC, ?_⟩
  intro R hR F hF c hc lam hlam B hB i
  have hlow := rightGram_eigenvalue_lower_of_direction_bound B (a / R)
    (div_nonneg ha.le (by linarith)) (hframe R hR F hF c hc lam hlam B hB) i
  exact hscalar R _ hR ((frame_rightGram_posDef B).eigenvalues_pos i) hlow
    (minimizing_rightGram_eigenvalues_le_one F c lam hlam B hB i)

theorem source_minimizing_log_bounds (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      euclideanFrameOperatorNorm (CFC.log (B.valᵀ * B.val)) ≤ C * sourceLogScale CX R ∧
      |Matrix.trace (CFC.log (B.valᵀ * B.val))| ≤ 3 * C * sourceLogScale CX R := by
  obtain ⟨C, hC, he⟩ := minimizing_log_eigenvalues_bound k X hX CX hCX
  refine ⟨C, hC, ?_⟩
  intro R hR F hF c hc B hB
  have hb := he R hR F hF c hc _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le B hB
  constructor
  · exact sourceMatrix_log_norm_le_of_eigenvalue_bounds _ (frame_rightGram_posDef B) _
      (mul_nonneg hC.le (sourceLogScale_pos CX R hCX hR).le) hb
  · simpa only [mul_assoc] using sourceMatrix_abs_trace_log_le_of_eigenvalue_bounds _
      (frame_rightGram_posDef B) _ hb

theorem minimizing_weightedJet_square_le_of_trace_log {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (M : ℝ) (hM : |Matrix.trace (CFC.log (B.valᵀ * B.val))| ≤ M) :
    ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (jetTensorHSNorm F c B.val r) ^ 2 ≤ 3 + 2 * lam * M := by
  have htr : 0 ≤ Matrix.trace (B.valᵀ * B.val) :=
    Finset.sum_nonneg (fun i _ => real_posSemidef_diag_nonneg _ (frame_rightGram_posDef B).posSemidef i)
  have hb := minimizing_trace_balance F c lam B hB
  have hlog := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hM)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlam)
  nlinarith only [htr, hb, hlog]

theorem source_minimizing_weightedJet_square_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ W : ℝ, 0 < W ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (jetTensorHSNorm F c B.val r) ^ 2 ≤ W := by
  obtain ⟨C, hC, hb⟩ := source_minimizing_log_bounds k X hX CX C0 hCX hC0
  have hbase : 0 < C0 * sourceLogScale CX 2 :=
    mul_pos (by linarith) (sourceLogScale_pos CX 2 hCX (by norm_num))
  refine ⟨3 + 6 * C * (C0 * sourceLogScale CX 2)⁻¹, by positivity, ?_⟩
  intro R hR F hF c hc B hB
  have htrace := (hb R hR F hF c hc B hB).2
  have h := minimizing_weightedJet_square_le_of_trace_log F c _
    (sourceRegularization_pos CX C0 R hCX hC0 hR).le B hB _ htrace
  have hscale := sourceRegularization_scale_bound CX C0 hCX hC0 R hR
  calc
    _ ≤ 3 + 2 * sourceRegularization CX C0 R * (3 * C * sourceLogScale CX R) := h
    _ = 3 + 6 * C * (sourceRegularization CX C0 R * sourceLogScale CX R) := by ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hscale (by positivity)) _

theorem jet_sum_le_of_weighted_square_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (W : ℝ) (hW : 0 ≤ W)
    (h : ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (jetTensorHSNorm F c B r) ^ 2 ≤ W) :
    ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ ((k : ℝ) + 1) * (1 + W) := by
  have he : ∀ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ 1 + W := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by have := (Finset.mem_Icc.mp hr).1; omega)
    have ht : (r : ℝ) * (jetTensorHSNorm F c B r) ^ 2 ≤ W :=
      (Finset.single_le_sum (fun n _ => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) hr).trans h
    have hs : (jetTensorHSNorm F c B r) ^ 2 ≤ W := by
      calc
        _ ≤ (r : ℝ) * (jetTensorHSNorm F c B r) ^ 2 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 (sq_nonneg (jetTensorHSNorm F c B r))
        _ ≤ W := ht
    nlinarith [sq_nonneg (jetTensorHSNorm F c B r - 1)]
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 2 k, (1 + W) := Finset.sum_le_sum he
    _ = ((Finset.Icc 2 k).card : ℝ) * (1 + W) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * (1 + W) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      rw [Nat.card_Icc]
      exact_mod_cast Nat.sub_le (k + 1) 2

theorem source_minimizing_uniform_jet_window (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ M : ℝ, 0 < M ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B.val r ≤ M := by
  obtain ⟨W, hW, hw⟩ := source_minimizing_weightedJet_square_bound k X hX CX C0 hCX hC0
  refine ⟨((k : ℝ) + 1) * (1 + W), by positivity, ?_⟩
  intro R hR F hF c hc B hB
  exact jet_sum_le_of_weighted_square_bound F c B.val W hW.le (hw R hR F hF c hc B hB)

theorem source_minimizing_quantitative_bounds (k : ℕ) (hk : 2 ≤ k)
    (X : Set PhysicalSpace) (hX : Bornology.IsBounded X)
    (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ a M : ℝ, 0 < a ∧ 0 < M ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ F : CoefficientSpace k, coefficientEuclideanNorm F ≤ 2 * R →
      ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      euclideanFrameOperatorNorm B.val ≤ 1 ∧
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B.val r ≤ M) ∧
      ∀ u : PhysicalSpace, (a / R * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u)) ∧
        (a * (physicalEuclideanNorm u) ^ 2 ≤ augmentedTranslationQuadratic F c B.val u) := by
  obtain ⟨a, ha, hboth⟩ := source_minimizing_frame_and_stopping_common_constant k hk X hX
  obtain ⟨M, hM, hw⟩ := source_minimizing_uniform_jet_window k X hX CX C0 hCX hC0
  refine ⟨a, M, ha, hM, ?_⟩
  intro R hR F hF c hc B hB
  exact ⟨source_minimizing_euclideanFrameOperatorNorm_le_one F c CX C0 R hCX hC0 hR B hB,
    hw R hR F hF c hc B hB, hboth CX C0 R hCX hC0 hR F hF c hc B hB⟩

end PaperI
