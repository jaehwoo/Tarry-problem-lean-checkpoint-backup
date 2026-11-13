import PaperILean.BalanceSpectralBounds
import PaperILean.TensorFrameBounds

/-! I256-265: apply the generic spectral argument to actual attained minima.
All natural degrees and all nonnegative regularizations are allowed. The source
positive regularization is a specialization, not a new hypothesis. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def weightedJetContractionGram {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B r

theorem weightedJetContractionGram_posSemidef {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (weightedJetContractionGram F c B).PosSemidef := by
  have hsum : ∀ s : Finset ℕ,
      (∑ r ∈ s, (r : ℝ) • jetContractionGram F c B r).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef)
    | @insert r s hr ih =>
      rw [Finset.sum_insert hr]
      exact (real_posSemidef_smul _ (jetContractionGram_posSemidef F c B r) _
        (Nat.cast_nonneg r)).add ih
  exact hsum _

theorem minimizing_rightGram_eigenvalues_le_one {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (i : Fin 3) : (frame_rightGram_posDef B).isHermitian.eigenvalues i ≤ 1 :=
  balance_eigenvalues_le_one _ (weightedJetContractionGram F c B.val)
    (frame_rightGram_posDef B) (weightedJetContractionGram_posSemidef F c B.val)
    lam hlam (frame_balance_of_minimum F c lam B hB) i

theorem minimizing_neg_log_posSemidef {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    (-CFC.log (B.valᵀ * B.val)).PosSemidef :=
  neg_log_posSemidef_of_eigenvalues_le_one _ (frame_rightGram_posDef B)
    (minimizing_rightGram_eigenvalues_le_one F c lam hlam B hB)

theorem minimizing_one_sub_rightGram_posSemidef {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    (1 - B.valᵀ * B.val).PosSemidef :=
  one_sub_posSemidef_of_eigenvalues_le_one _ (frame_rightGram_posDef B)
    (minimizing_rightGram_eigenvalues_le_one F c lam hlam B hB)

theorem minimizing_gram_dominance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    (B.valᵀ * B.val + weightedJetContractionGram F c B.val - 1).PosSemidef :=
  balance_gram_dominance _ _ (frame_rightGram_posDef B)
    (weightedJetContractionGram_posSemidef F c B.val) lam hlam
    (frame_balance_of_minimum F c lam B hB)

theorem physicalEuclideanNorm_sq_eq_dotProduct (u : PhysicalSpace) :
    (physicalEuclideanNorm u) ^ 2 = dotProduct u u := by
  rw [physicalEuclideanNorm, coordinateL2Norm_sq]
  simp only [dotProduct, pow_two]

theorem rightGram_quadratic (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    dotProduct u ((Bᵀ * B) *ᵥ u) = (physicalEuclideanNorm (B *ᵥ u)) ^ 2 := by
  rw [physicalEuclideanNorm_sq_eq_dotProduct, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem physicalEuclideanNorm_mulVec_le_of_gram_le_one
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : (1 - Bᵀ * B).PosSemidef)
    (u : PhysicalSpace) : physicalEuclideanNorm (B *ᵥ u) ≤ physicalEuclideanNorm u := by
  have h := hB.2 u
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    rightGram_quadratic, ← physicalEuclideanNorm_sq_eq_dotProduct] at h
  nlinarith [physicalEuclideanNorm_nonneg u, physicalEuclideanNorm_nonneg (B *ᵥ u)]

theorem minimizing_physicalEuclideanNorm_mulVec_le {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (u : PhysicalSpace) : physicalEuclideanNorm (B.val *ᵥ u) ≤ physicalEuclideanNorm u :=
  physicalEuclideanNorm_mulVec_le_of_gram_le_one _
    (minimizing_one_sub_rightGram_posSemidef F c lam hlam B hB) u

theorem minimizing_euclideanFrameOperatorNorm_le_one {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    euclideanFrameOperatorNorm B.val ≤ 1 := by
  apply (euclideanFrameOperatorNorm_le_iff B.val 1 zero_le_one).mpr
  simpa only [one_mul] using minimizing_physicalEuclideanNorm_mulVec_le F c lam hlam B hB

theorem source_minimizing_euclideanFrameOperatorNorm_le_one {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (CX C0 R : ℝ)
    (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
      FrameEnergy F c (sourceRegularization CX C0 R) D.val) :
    euclideanFrameOperatorNorm B.val ≤ 1 :=
  minimizing_euclideanFrameOperatorNorm_le_one F c _
    (sourceRegularization_pos CX C0 R hCX hC0 hR).le B hB

theorem weightedJetContractionGram_trace {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (weightedJetContractionGram F c B) =
      ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (jetTensorHSNorm F c B r) ^ 2 := by
  simp only [weightedJetContractionGram, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [jetContractionGram_trace F c B r (by have := (Finset.mem_Icc.mp hr).1; omega)]

theorem minimizing_trace_balance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    Matrix.trace (B.valᵀ * B.val) +
      (∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (jetTensorHSNorm F c B.val r) ^ 2) +
      2 * lam * Matrix.trace (CFC.log (B.valᵀ * B.val)) = 3 := by
  have h := congrArg Matrix.trace (frame_balance_of_minimum F c lam B hB)
  change Matrix.trace (B.valᵀ * B.val + weightedJetContractionGram F c B.val +
    (2 * lam) • CFC.log (B.valᵀ * B.val)) = Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) at h
  simpa only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    weightedJetContractionGram_trace, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] using h

end PaperI
