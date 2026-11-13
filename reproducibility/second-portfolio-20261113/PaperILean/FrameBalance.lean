import PaperILean.MatrixFrameFirstVariation
import PaperILean.FrameMinimumUniqueness
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The exact first variation and balance equation, I229-232 and I250-254.
The order-zero extension of the Gram family is unused by the energy (r=2..k).
The minimum is an attained minimum of the original energy; smooth selection
of a minimum is not assumed. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def jetContractionGram {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => 0
  | n + 1 => tensorContractionGram (affineJetTensor F c B (n + 1))

theorem jetContractionGram_succ {k n : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    jetContractionGram F c B (n + 1) = tensorContractionGram (affineJetTensor F c B (n + 1)) := rfl

theorem jetContractionGram_posSemidef {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) : (jetContractionGram F c B r).PosSemidef := by
  cases r with
  | zero => exact Matrix.PosSemidef.zero
  | succ n => exact tensorContractionGram_posSemidef _

theorem jetContractionGram_isSymm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) : (jetContractionGram F c B r).IsSymm :=
  (realMatrix_isHermitian_iff_isSymm _).mp (jetContractionGram_posSemidef F c B r).isHermitian

theorem jetContractionGram_quadratic {k n : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : PhysicalSpace) :
    dotProduct u (jetContractionGram F c B (n + 1) *ᵥ u) =
      (tensorHSNorm ((affineJetTensor F c B (n + 1)).curryLeft u)) ^ 2 :=
  tensorContractionGram_quadratic _ u

theorem jetContractionGram_trace {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) (hr : 0 < r) :
    Matrix.trace (jetContractionGram F c B r) = (jetTensorHSNorm F c B r) ^ 2 := by
  cases r with
  | zero => omega
  | succ n => rw [jetContractionGram_succ, tensorContractionGram_trace, tensorHSNorm_affineJetTensor]

theorem hasDerivAt_jetTensorHSNorm_sq_frame_gram {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (r : ℕ) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (jetTensorHSNorm F c (B * NormedSpace.exp ℝ (t • H)) r) ^ 2)
      (2 * ((r : ℝ) * Matrix.trace (jetContractionGram F c B r * H))) 0 := by
  cases r with
  | zero => omega
  | succ n => simpa only [jetContractionGram_succ, Nat.cast_add, Nat.cast_one, mul_assoc] using
      hasDerivAt_affineJet_energyCurve_gram_zero F c B H hH (n := n)

def frameBalanceMatrix {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Bᵀ * B + (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B r) - 1 +
    (2 * lam) • CFC.log (Bᵀ * B)

theorem frameBalanceMatrix_isSymm {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) : (frameBalanceMatrix F c lam B).IsSymm := by
  have hsum : (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B r).IsSymm := by
    change (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B r)ᵀ = _
    simp only [Matrix.transpose_sum, Matrix.transpose_smul, (jetContractionGram_isSymm F c B _).eq]
  have hgram : (Bᵀ * B).IsSymm := by simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact ((hgram.add hsum).sub (Matrix.isSymm_one)).add
    (((realMatrix_isSelfAdjoint_iff_isSymm _).mp (IsSelfAdjoint.log (a := Bᵀ * B))).smul _)

theorem hasDerivAt_frameEnergyCurve_balance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    HasDerivAt (frameEnergyCurve F c lam B H)
      (2 * Matrix.trace (frameBalanceMatrix F c lam B.val * H)) 0 := by
  have ht := HasDerivAt.sum (u := Finset.Icc 2 k) (fun r hr =>
    hasDerivAt_jetTensorHSNorm_sq_frame_gram F c B.val H hH r
      (by have := (Finset.mem_Icc.mp hr).1; omega))
  have hd := ((hasDerivAt_const (0 : ℝ) (Real.log B.val.det)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.trace H))).const_mul 2
  have h := (((hasDerivAt_matrixFullHSNorm_sq_frame_zero B.val H).add ht).sub hd).add
    ((hasDerivAt_frameLogEnergyCurve_zero B H hH).const_mul lam)
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH]
  convert h using 1
  simp only [frameBalanceMatrix, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, zero_add, one_mul]
  rw [← Finset.mul_sum]
  ring

theorem frameEnergyCurve_first_derivative_balance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (frameEnergyCurve F c lam B H) 0 =
      2 * Matrix.trace (frameBalanceMatrix F c lam B.val * H) :=
  (hasDerivAt_frameEnergyCurve_balance F c lam B H hH).deriv

theorem frameBalanceMatrix_eq_zero_of_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    frameBalanceMatrix F c lam B.val = 0 := by
  let M := frameBalanceMatrix F c lam B.val
  have hM : M.IsSymm := frameBalanceMatrix_isSymm F c lam B.val
  have hmin : IsLocalMin (frameEnergyCurve F c lam B M) 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ) _ Filter.univ_mem
    intro t _
    rw [frameEnergyCurve_at_zero]
    exact hB (recenteredPositiveFrame B M hM t)
  have hz := hmin.hasDerivAt_eq_zero (hasDerivAt_frameEnergyCurve_balance F c lam B M hM)
  change 2 * Matrix.trace (M * M) = 0 at hz
  rw [← pow_two, trace_matrix_square_eq_fullHS M hM] at hz
  exact (matrixFullHSNorm_eq_zero_iff M).mp (by nlinarith [sq_nonneg (matrixFullHSNorm M)])

theorem frame_balance_of_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    B.valᵀ * B.val + (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B.val r) +
      (2 * lam) • CFC.log (B.valᵀ * B.val) = 1 := by
  have h := frameBalanceMatrix_eq_zero_of_minimum F c lam B hB
  unfold frameBalanceMatrix at h
  apply sub_eq_zero.mp
  convert h using 1 <;> abel

theorem exists_FrameEnergy_minimum_with_balance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) ∧
      B.valᵀ * B.val + (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B.val r) +
        (2 * lam) • CFC.log (B.valᵀ * B.val) = 1 := by
  obtain ⟨S, hS, hmin⟩ := exists_FrameEnergy_minimum F c lam hlam
  let B : PositiveFrame := ⟨S, hS.det_pos⟩
  exact ⟨B, hmin, frame_balance_of_minimum F c lam B hmin⟩

theorem exists_sourceFrameEnergy_minimum_with_balance {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    ∃ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) ∧
      B.valᵀ * B.val + (∑ r ∈ Finset.Icc 2 k, (r : ℝ) • jetContractionGram F c B.val r) +
        (2 * sourceRegularization CX C0 R) • CFC.log (B.valᵀ * B.val) = 1 :=
  exists_FrameEnergy_minimum_with_balance F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le

end PaperI
