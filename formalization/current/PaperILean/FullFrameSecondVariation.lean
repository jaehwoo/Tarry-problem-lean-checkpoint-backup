import PaperILean.MatrixFrameSecondVariation
import PaperILean.FrameBalance

/-! Full actual second variation of the unchanged energy at I205-212,
and the quantitative lower bound at I282. No minimum premise is needed
for this path calculation; the separate Frechet-Hessian bridge is not a
definition of a Hessian by a directional second derivative. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

def frameJetEnergyCurve {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 k, tensorFrameEnergyCurve (affineJetTensor F c B r) H t

theorem frameJetEnergyCurve_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (frameJetEnergyCurve F c B H) :=
  Differentiable.sum (fun r _ => tensorFrameEnergyCurve_differentiable _ H hH)

theorem frameJetEnergyCurve_deriv_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (frameJetEnergyCurve F c B H)) :=
  differentiable_deriv_finset_sum _ _
    (fun r _ => tensorFrameEnergyCurve_differentiable _ H hH)
    (fun r _ => tensorFrameEnergyCurve_deriv_differentiable _ H hH)

theorem frameJetEnergyCurve_second_derivative_zero {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (frameJetEnergyCurve F c B H)) 0 =
      4 * ∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B r))) ^ 2 := by
  unfold frameJetEnergyCurve
  rw [deriv2_finset_sum _ _
    (fun r _ => tensorFrameEnergyCurve_differentiable _ H hH)
    (fun r _ => tensorFrameEnergyCurve_deriv_differentiable _ H hH)]
  simp only [tensorFrameEnergyCurve_second_derivative_zero _ H hH, Finset.mul_sum]

theorem frameNonlogEnergyCurve_eq_components {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    frameNonlogEnergyCurve F c B H = fun t =>
      matrixFrameEnergyCurve B.val H t + frameJetEnergyCurve F c B.val H t -
        2 * (Real.log B.val.det + t * Matrix.trace H) := by
  funext t
  simp only [frameNonlogEnergyCurve, matrixFrameEnergyCurve, frameJetEnergyCurve]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (affineJet_energyCurve_eq F c B.val H) t

theorem frameNonlogEnergyCurve_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (frameNonlogEnergyCurve F c B H) := by
  rw [frameNonlogEnergyCurve_eq_components]
  exact ((matrixFrameEnergyCurve_differentiable B.val H hH).add
    (frameJetEnergyCurve_differentiable F c B.val H hH)).sub (by fun_prop)

theorem frameNonlogEnergyCurve_deriv_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (frameNonlogEnergyCurve F c B H)) := by
  rw [frameNonlogEnergyCurve_eq_components]
  have hd : deriv (fun t : ℝ => 2 * (Real.log B.val.det + t * Matrix.trace H)) =
      fun _ => 2 * Matrix.trace H := by
    funext t
    simpa using (((hasDerivAt_const t (Real.log B.val.det)).add
      ((hasDerivAt_id t).mul_const (Matrix.trace H))).const_mul 2).deriv
  apply differentiable_deriv_sub
  · exact (matrixFrameEnergyCurve_differentiable B.val H hH).add
      (frameJetEnergyCurve_differentiable F c B.val H hH)
  · fun_prop
  · exact differentiable_deriv_add _ _
      (matrixFrameEnergyCurve_differentiable B.val H hH)
      (frameJetEnergyCurve_differentiable F c B.val H hH)
      (matrixFrameEnergyCurve_deriv_differentiable B.val H hH)
      (frameJetEnergyCurve_deriv_differentiable F c B.val H hH)
  · rw [hd]; exact differentiable_const _

theorem frameNonlogEnergyCurve_second_derivative_zero {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (frameNonlogEnergyCurve F c B H)) 0 =
      4 * (matrixFullHSNorm (B.val * H)) ^ 2 +
      4 * ∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B.val r))) ^ 2 := by
  have hp := matrixFrameEnergyCurve_differentiable B.val H hH
  have hp' := matrixFrameEnergyCurve_deriv_differentiable B.val H hH
  have hj := frameJetEnergyCurve_differentiable F c B.val H hH
  have hj' := frameJetEnergyCurve_deriv_differentiable F c B.val H hH
  have hd : deriv (fun t : ℝ => 2 * (Real.log B.val.det + t * Matrix.trace H)) =
      fun _ => 2 * Matrix.trace H := by
    funext t
    simpa using (((hasDerivAt_const t (Real.log B.val.det)).add
      ((hasDerivAt_id t).mul_const (Matrix.trace H))).const_mul 2).deriv
  rw [frameNonlogEnergyCurve_eq_components, deriv2_sub _ _ (hp.add hj) (by fun_prop)
    (differentiable_deriv_add _ _ hp hj hp' hj') (by rw [hd]; exact differentiable_const _),
    deriv2_add _ _ hp hj hp' hj', hd, deriv_const, sub_zero,
    matrixFrameEnergyCurve_second_derivative_zero B.val H hH,
    frameJetEnergyCurve_second_derivative_zero F c B.val H hH]

theorem frameEnergyCurve_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (frameEnergyCurve F c lam B H) := by
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH]
  exact (frameNonlogEnergyCurve_differentiable F c B H hH).add
    ((frameLogEnergyCurve_differentiable B H hH).const_mul lam)

theorem frameEnergyCurve_deriv_differentiable {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    Differentiable ℝ (deriv (frameEnergyCurve F c lam B H)) := by
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH]
  exact differentiable_deriv_add _ _
    (frameNonlogEnergyCurve_differentiable F c B H hH)
    ((frameLogEnergyCurve_differentiable B H hH).const_mul lam)
    (frameNonlogEnergyCurve_deriv_differentiable F c B H hH)
    (differentiable_deriv_const_mul _ (frameLogEnergyCurve_differentiable B H hH)
      (frameLogEnergyCurve_deriv_differentiable B H hH) lam)

theorem frameEnergyCurve_second_derivative_zero {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    deriv (deriv (frameEnergyCurve F c lam B H)) 0 =
      4 * (matrixFullHSNorm (B.val * H)) ^ 2 +
      4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B.val r))) ^ 2) +
      lam * deriv (deriv (frameLogEnergyCurve B H)) 0 := by
  have hl := frameLogEnergyCurve_differentiable B H hH
  have hl' := frameLogEnergyCurve_deriv_differentiable B H hH
  rw [frameEnergyCurve_eq_nonlog_add_log F c lam B H hH,
    deriv2_add _ _ (frameNonlogEnergyCurve_differentiable F c B H hH) (hl.const_mul lam)
      (frameNonlogEnergyCurve_deriv_differentiable F c B H hH)
      (differentiable_deriv_const_mul _ hl hl' lam), deriv2_const_mul _ hl hl',
    frameNonlogEnergyCurve_second_derivative_zero F c B H hH]

theorem frameEnergyCurve_second_derivative_ge {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    4 * (matrixFullHSNorm (B.val * H)) ^ 2 +
      4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B.val r))) ^ 2) +
      8 * lam * (matrixFullHSNorm H) ^ 2 ≤
        deriv (deriv (frameEnergyCurve F c lam B H)) 0 := by
  rw [frameEnergyCurve_second_derivative_zero F c lam B H hH]
  have h := mul_le_mul_of_nonneg_left (frameLogEnergyCurve_second_derivative_ge_HS_at B H hH 0) hlam
  nlinarith

theorem frameEnergyCurve_second_derivative_ge_tensor {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) :
    4 * (∑ r ∈ Finset.Icc 2 k, (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B.val r))) ^ 2) +
      8 * lam * (matrixFullHSNorm H) ^ 2 ≤
        deriv (deriv (frameEnergyCurve F c lam B H)) 0 := by
  have := frameEnergyCurve_second_derivative_ge F c lam hlam B H hH
  nlinarith [sq_nonneg (matrixFullHSNorm (B.val * H))]

theorem frameEnergyCurve_second_derivative_pos {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hne : H ≠ 0) :
    0 < deriv (deriv (frameEnergyCurve F c lam B H)) 0 := by
  have h := frameEnergyCurve_second_derivative_ge_tensor F c lam hlam.le B H hH
  have hn : matrixFullHSNorm H ≠ 0 := fun hz => hne ((matrixFullHSNorm_eq_zero_iff H).mp hz)
  have hs : 0 ≤ ∑ r ∈ Finset.Icc 2 k,
      (tensorHSNorm (tensorSlotAction H (affineJetTensor F c B.val r))) ^ 2 :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hp : 0 < 8 * lam * (matrixFullHSNorm H) ^ 2 := by positivity
  linarith

end PaperI
