import PaperILean.FrameEnergyMixedDerivative
import PaperILean.MinimizerJetBounds
import PaperILean.SymmetricFrameChartHessian
import PaperILean.HorizontalFrameAlgebra

/-! I296: quantitative consequence of the exact differentiated-criticality
identity. The latter is an explicit hypothesis and remains unformalized as
an application to moving minimizing frames. Constants precede R,F,c,B,h,S.
I298: actual inverse differentiation, independently of any continuation claim.
-/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem abs_tensorHSInner_le {r : ℕ} (T U : TensorSpace r) :
    |tensorHSInner T U| ≤ tensorHSNorm T * tensorHSNorm U := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (tensorHSNorm_nonneg T)
    (tensorHSNorm_nonneg U))).mp
  simpa only [sq_abs, tensorHSInner, mul_pow, tensorHSNorm_sq] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (tensorCoordinates T) (tensorCoordinates U)

theorem successor_jet_norm_le_window {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ j ∈ Finset.Icc 2 k, jetTensorHSNorm F c B j ≤ M)
    {r : ℕ} (hr : r ∈ Finset.Icc 2 (k - 1)) :
    tensorHSNorm (affineJetTensor F c B (r + 1)) ≤ M := by
  have hm : r + 1 ∈ Finset.Icc 2 k := by
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.Icc 2 k) =>
    jetTensorHSNorm_nonneg F c B j) hm
  exact (by simpa only [tensorHSNorm_affineJetTensor] using he.trans hM)

theorem tensorSlotHSNorm_le_sqrt_hessian {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (S : SymmetricMatrix 3) {r : ℕ} (hr : r ∈ Finset.Icc 2 k) :
    tensorHSNorm (tensorSlotAction S.val (affineJetTensor F c B.val r)) ≤
      Real.sqrt (symmetricFrameEnergyHessian F c lam B S S) := by
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc 2 k,
      (tensorHSNorm (tensorSlotAction S.val (affineJetTensor F c B.val j))) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone := Finset.single_le_sum (fun j (_ : j ∈ Finset.Icc 2 k) =>
    sq_nonneg (tensorHSNorm (tensorSlotAction S.val (affineJetTensor F c B.val j)))) hr
  have hh := symmetricFrameEnergyHessian_ge F c lam hlam B S
  have hp : 0 ≤ 8 * lam * (matrixFullHSNorm S.val) ^ 2 := by positivity
  have hE : 0 ≤ symmetricFrameEnergyHessian F c lam B S S := by linarith
  apply (Real.le_sqrt (tensorHSNorm_nonneg _) hE).mpr
  nlinarith

theorem mixed_sum_abs_le_hessian_sqrt {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (B : PositiveFrame)
    (h : PhysicalSpace) (S : SymmetricMatrix 3) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∑ j ∈ Finset.Icc 2 k, jetTensorHSNorm F c B.val j ≤ M) :
    |∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h S.val r| ≤
      ((k : ℝ) + 1) * M * physicalEuclideanNorm h *
        Real.sqrt (symmetricFrameEnergyHessian F c lam B S S) := by
  let E := symmetricFrameEnergyHessian F c lam B S S
  have hterm : ∀ r ∈ Finset.Icc 2 (k - 1),
      |jetCenterFrameMixedTerm F c B.val h S.val r| ≤
        M * physicalEuclideanNorm h * Real.sqrt E := by
    intro r hr
    have hwin := successor_jet_norm_le_window F c B.val M hM hr
    have hcon := tensorHSNorm_curryLeft_le (affineJetTensor F c B.val (r + 1)) h
    have hcon' : tensorHSNorm ((affineJetTensor F c B.val (r + 1)).curryLeft h) ≤
        M * physicalEuclideanNorm h := by
      nlinarith [physicalEuclideanNorm_nonneg h]
    have hr' : r ∈ Finset.Icc 2 k := by
      simp only [Finset.mem_Icc] at hr ⊢
      omega
    exact (abs_tensorHSInner_le _ _).trans (mul_le_mul hcon'
      (tensorSlotHSNorm_le_sqrt_hessian F c lam hlam B S hr')
      (tensorHSNorm_nonneg _) (mul_nonneg hM0 (physicalEuclideanNorm_nonneg h)))
  have hcard : ((Finset.Icc 2 (k - 1)).card : ℝ) ≤ (k : ℝ) + 1 := by
    have hh : (Finset.Icc 2 (k - 1)).card ≤ k + 1 := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast hh
  calc
    |∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h S.val r|
        ≤ ∑ r ∈ Finset.Icc 2 (k - 1), |jetCenterFrameMixedTerm F c B.val h S.val r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.Icc 2 (k - 1), M * physicalEuclideanNorm h * Real.sqrt E :=
      Finset.sum_le_sum hterm
    _ = ((Finset.Icc 2 (k - 1)).card : ℝ) * (M * physicalEuclideanNorm h * Real.sqrt E) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * (M * physicalEuclideanNorm h * Real.sqrt E) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hM0 (physicalEuclideanNorm_nonneg h)) (Real.sqrt_nonneg E))
    _ = _ := by ring

theorem scalar_generator_bound {lam E a u : ℝ} (hlam : 0 < lam)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hlower : 8 * lam * u ^ 2 ≤ E)
    (hupper : E ≤ 4 * a * Real.sqrt E) : u ≤ 4 * a / Real.sqrt lam := by
  have hE : 0 ≤ E := le_trans (by positivity) hlower
  have hsq := Real.sq_sqrt hE
  have hlamsq := Real.sq_sqrt hlam.le
  have hx : Real.sqrt E ≤ 4 * a := by
    nlinarith [Real.sqrt_nonneg E]
  have hu' : Real.sqrt lam * u ≤ Real.sqrt E := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg lam) hu) (Real.sqrt_nonneg E)).mp
    rw [mul_pow, hlamsq, hsq]
    nlinarith [mul_nonneg hlam.le (sq_nonneg u)]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hlam)).mpr
  nlinarith

theorem horizontal_generator_bound_of_criticality {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (h : PhysicalSpace) (S : SymmetricMatrix 3) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∑ j ∈ Finset.Icc 2 k, jetTensorHSNorm F c B.val j ≤ M)
    (hcrit : symmetricFrameEnergyHessian F c lam B S S =
      -4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h S.val r) :
    matrixFullHSNorm S.val ≤ (4 * ((k : ℝ) + 1) * M) / Real.sqrt lam * physicalEuclideanNorm h := by
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc 2 k,
      (tensorHSNorm (tensorSlotAction S.val (affineJetTensor F c B.val j))) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := symmetricFrameEnergyHessian_ge F c lam hlam.le B S
  have hlower : 8 * lam * (matrixFullHSNorm S.val) ^ 2 ≤
      symmetricFrameEnergyHessian F c lam B S S := by linarith
  have hm := mixed_sum_abs_le_hessian_sqrt F c lam hlam.le B h S M hM0 hM
  have hupper : symmetricFrameEnergyHessian F c lam B S S ≤
      4 * (((k : ℝ) + 1) * M * physicalEuclideanNorm h) *
        Real.sqrt (symmetricFrameEnergyHessian F c lam B S S) := by
    have hn := neg_le_abs (∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h S.val r)
    nlinarith
  have hb := scalar_generator_bound hlam
    (mul_nonneg (mul_nonneg (by positivity) hM0) (physicalEuclideanNorm_nonneg h))
    (matrixFullHSNorm_nonneg S.val) hlower hupper
  convert hb using 1 <;> ring

theorem source_horizontal_generator_bound_of_criticality (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c (sourceRegularization CX C0 R) B.val ≤
        FrameEnergy F c (sourceRegularization CX C0 R) D.val) →
      ∀ h : PhysicalSpace, ∀ S : SymmetricMatrix 3,
      (symmetricFrameEnergyHessian F c (sourceRegularization CX C0 R) B S S =
        -4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F c B.val h S.val r) →
      matrixFullHSNorm S.val ≤ K / Real.sqrt (sourceRegularization CX C0 R) * physicalEuclideanNorm h := by
  obtain ⟨M, hM, hw⟩ := source_minimizing_uniform_jet_window k X hX CX C0 hCX hC0
  refine ⟨4 * ((k : ℝ) + 1) * M, by positivity, ?_⟩
  intro R hR F hF c hc B hB h S hcrit
  exact horizontal_generator_bound_of_criticality F c (sourceRegularization CX C0 R)
    (sourceRegularization_pos CX C0 R hCX hC0 hR) B h S M hM.le
    (hw R hR F hF c hc B hB) hcrit

theorem hasDerivAt_matrix_inverse {n : ℕ} {B : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hB : HasDerivAt B V t) (hu : IsUnit (B t)) :
    HasDerivAt (fun s => (B s)⁻¹) (-(B t)⁻¹ * V * (B t)⁻¹) t := by
  obtain ⟨U, hU⟩ := hu
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) U
  rw [hU] at hi
  have hd := hi.comp_hasDerivAt t hB
  simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    Matrix.coe_units_inv, hU, neg_mul] using hd

theorem hasDerivAt_inverse_horizontal {n : ℕ} {B : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {S : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hB : HasDerivAt B (B t * S) t) (hu : IsUnit (B t)) :
    HasDerivAt (fun s => (B s)⁻¹) (-S * (B t)⁻¹) t := by
  have hd := hasDerivAt_matrix_inverse hB hu
  have hi := Matrix.nonsing_inv_mul (B t) ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  simpa only [← Matrix.mul_assoc, neg_mul, hi, Matrix.one_mul] using hd

end PaperI
