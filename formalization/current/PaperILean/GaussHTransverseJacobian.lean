import PaperILean.GaussHDerivative
import PaperILean.NullGraphRawConstraints
import PaperILean.PhysicalGaussPivot
import PaperILean.OriginalUpperNormalPullback

/-! I2379[0,131): the actual Gauss H transverse derivative, in source column
order (Tx,Ty,C,D). This is the algebraic stage before the density inference.
Only the parent constant is discarded. No area formula or Haar bound is asserted. -/

noncomputable section
namespace PaperI.GaussHTransverseJacobian

open Filter PaperI.NormalFibers PaperI.NullGraphRawConstraints PaperI.GaussHDerivative
open scoped Topology

/-- Actual upper-affine H coordinates in the manuscript's column order. -/
noncomputable def sourceCoordinates (q : FrameSpace) : Fin 6 → ℝ :=
  ![0, q 2, q 0, q 3, q 1, 0]

/-- The four raw Gauss rows of the original full normal derivative. -/
noncomputable def parentRows {k : ℕ} (J : CoefficientSpace k) (m : ℕ) : FrameSpace :=
  let G := originalNormalPolynomial J (m - 1)
  ![MvPolynomial.eval 0 G,
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))]

/-- The parent is pulled back and bracketed before any positive differentiation. -/
noncomputable def bracketedRawHConstraints {k : ℕ} (J : CoefficientSpace k)
    (m : ℕ) (q : FrameSpace) : FrameSpace :=
  let P := pullback ![q 0, 0, q 2, q 3] (q 1) 0 (coefficientPolynomial J)
  let G := iteratedPolynomialPartial (m - 1) (fun _ => 0)
    (P - MvPolynomial.C (MvPolynomial.eval 0 P))
  ![MvPolynomial.eval 0 G,
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 G),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G))]

theorem bracketedRawHConstraints_eq {k : ℕ} (J : CoefficientSpace k) (m : ℕ)
    (hm : 2 ≤ m) :
    bracketedRawHConstraints J m = Hmap (originalNormalPolynomial J (m - 1)) := by
  have ho : m - 1 = (m - 2) + 1 := by omega
  funext q
  unfold bracketedRawHConstraints Hmap normalizationEquationsI originalNormalPolynomial
  dsimp only
  rw [ho, iterated_x_sub_constant, iterated_x_pullback]

private theorem affine_pullback (q : FrameSpace) (P : Poly) :
    affinePolynomialMap ![(sourceCoordinates q) 2, (sourceCoordinates q) 4,
        (sourceCoordinates q) 5] (originalUpperLinearMatrix (sourceCoordinates q)) P =
      pullback ![q 0, 0, q 2, q 3] (q 1) 0 P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [affinePolynomialMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, hP, map_mul]
      congr 1
      fin_cases i <;>
        simp [affinePolynomialMap, affineCoordinate, originalUpperLinearMatrix,
          sourceCoordinates, frameVariables, Fin.sum_univ_succ] <;> ring

/-- Literal equality with the original coefficient action; no desired matrix is assumed. -/
theorem bracketedRawHConstraints_eq_coefficient_action {k : ℕ}
    (J : CoefficientSpace k) (m : ℕ) :
    bracketedRawHConstraints J m =
      fun q => parentRows (originalUpperCoefficientPullback J (sourceCoordinates q)) m := by
  funext q
  have hp : MvPolynomial.eval 0
      (pullback ![q 0, 0, q 2, q 3] (q 1) 0 (coefficientPolynomial J)) =
      phase J ![q 0, q 1, 0] := by
    rw [eval_pullback_zero, eval_coefficientPolynomial]
    rfl
  unfold bracketedRawHConstraints parentRows originalNormalPolynomial
  rw [originalUpperCoefficientPullback, polynomial_affineCoefficientMap, affine_pullback]
  dsimp only
  rw [hp]
  rfl

/-- Actual parent normalization Jacobian in source coordinates. -/
noncomputable def rawJacobian {k : ℕ} (J : CoefficientSpace k) (m : ℕ) :
    Matrix (Fin 4) (Fin 4) ℝ := ordinaryJacobian (bracketedRawHConstraints J m) 0

theorem rawJacobian_eq {k : ℕ} (J : CoefficientSpace k) (m : ℕ) (hm : 2 ≤ m) :
    rawJacobian J m = rawHJacobian (originalNormalPolynomial J (m - 1)) := by
  rw [rawJacobian, bracketedRawHConstraints_eq J m hm]
  rfl

/-- The actual raw Gauss matrix is lower triangular after its stated normalization. -/
theorem normalized_H_matrix (G : Poly) (hrows : Hmap G 0 = 0) :
    (∀ i j : Fin 4, i < j → rawHJacobian G i j = 0) ∧
      (∀ i : Fin 4, rawHJacobian G i i =
        ![MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G),
          MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G))] i) ∧
      (rawHJacobian G).det =
        (MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G)) ^ 2 *
          (MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G))) ^ 2 := by
  have hy : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G) = 0 := by
    simpa only [Hmap_zero, Matrix.cons_val_succ, Matrix.cons_val_zero, Pi.zero_apply]
      using congrFun hrows 1
  rw [rawHJacobian_eq_matrix]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hy]
  constructor
  · intro i
    fin_cases i <;> rfl
  · rw [hy, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three]
    ring

/-- The complete raw transverse-Jacobian stage for every positive normal order.
The upper manuscript range is unnecessary for this algebraic implication. -/
theorem gauss_h_transverse_jacobian_core {k : ℕ} (J : CoefficientSpace k)
    (m : ℕ) (hm : 2 ≤ m) (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J (m - 1) ![c v, v 0, v 1] = 0)
    (hκ : originalNormalPhase J m 0 ≠ 0) (hr : PhysicalGaussPivot.graphYY c ≠ 0)
    (hrows : bracketedRawHConstraints J m 0 = 0) :
    DifferentiableAt ℝ (bracketedRawHConstraints J m) 0 ∧
      (∀ i j : Fin 4, i < j → rawJacobian J m i j = 0) ∧
      (∀ i : Fin 4, rawJacobian J m i i =
        ![originalNormalPhase J m 0, -originalNormalPhase J m 0 * PhysicalGaussPivot.graphYY c,
          originalNormalPhase J m 0, -originalNormalPhase J m 0 * PhysicalGaussPivot.graphYY c] i) ∧
      (rawJacobian J m).det = (originalNormalPhase J m 0) ^ 4 * (PhysicalGaussPivot.graphYY c) ^ 2 ∧
      |(rawJacobian J m).det| = |originalNormalPhase J m 0| ^ 4 * |PhysicalGaussPivot.graphYY c| ^ 2 ∧
      (rawJacobian J m).det ≠ 0 := by
  let G := originalNormalPolynomial J (m - 1)
  have ho : m - 1 + 1 = m := by omega
  have hx : MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G) = originalNormalPhase J m 0 := by
    change MvPolynomial.eval 0
      (MvPolynomial.pderiv 0 (originalNormalPolynomial J (m - 1))) = _
    rw [← originalNormalPolynomial_succ, ho, ← originalNormalPhase_eq_eval]
  have hroot' : ∀ᶠ v in 𝓝 0, MvPolynomial.eval ![c v, v 0, v 1] G = 0 := by
    simpa only [originalNormalPhase_eq_eval] using hroot
  have hyy : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 G)) =
      -originalNormalPhase J m 0 * PhysicalGaussPivot.graphYY c := by
    have h := PhysicalGaussPivot.graph_yy_derivative G c hc hc0 hDc hroot' (by rwa [hx])
    simpa only [hx] using h
  have hrows' : Hmap G 0 = 0 := by
    simpa only [bracketedRawHConstraints_eq J m hm] using hrows
  obtain ⟨htri, hdiag, hdet⟩ := normalized_H_matrix G hrows'
  have hj : rawJacobian J m = rawHJacobian G := rawJacobian_eq J m hm
  have hd : (rawJacobian J m).det =
      (originalNormalPhase J m 0) ^ 4 * (PhysicalGaussPivot.graphYY c) ^ 2 := by
    rw [hj, hdet, hx, hyy]
    ring
  refine ⟨?_, ?_, ?_, hd, ?_, ?_⟩
  · rw [bracketedRawHConstraints_eq J m hm]
    exact (hasFDerivAt_Hmap_zero G).differentiableAt
  · simpa only [hj] using htri
  · simpa only [hj, hx, hyy] using hdiag
  · rw [hd, abs_mul, abs_pow, abs_pow]
  · rw [hd]
    exact mul_ne_zero (pow_ne_zero 4 hκ) (pow_ne_zero 2 hr)

/-- I2379[0,131), retaining the source range 2 <= m <= k/2.
The signed determinant is in source order (Tx,Ty,C,D), not the saved Haar order.
The joint coefficient density, measure disintegration and quantitative pivot are separate. -/
theorem gauss_h_transverse_jacobian_stage {k : ℕ} (J : CoefficientSpace k)
    (m : ℕ) (hm : 2 ≤ m) (_hmk : m ≤ k / 2) (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J (m - 1) ![c v, v 0, v 1] = 0)
    (hκ : originalNormalPhase J m 0 ≠ 0) (hr : PhysicalGaussPivot.graphYY c ≠ 0)
    (hrows : bracketedRawHConstraints J m 0 = 0) :
    DifferentiableAt ℝ (bracketedRawHConstraints J m) 0 ∧
      (∀ i j : Fin 4, i < j → rawJacobian J m i j = 0) ∧
      (∀ i : Fin 4, rawJacobian J m i i =
        ![originalNormalPhase J m 0, -originalNormalPhase J m 0 * PhysicalGaussPivot.graphYY c,
          originalNormalPhase J m 0, -originalNormalPhase J m 0 * PhysicalGaussPivot.graphYY c] i) ∧
      (rawJacobian J m).det = (originalNormalPhase J m 0) ^ 4 * (PhysicalGaussPivot.graphYY c) ^ 2 ∧
      |(rawJacobian J m).det| = |originalNormalPhase J m 0| ^ 4 * |PhysicalGaussPivot.graphYY c| ^ 2 ∧
      (rawJacobian J m).det ≠ 0 :=
  gauss_h_transverse_jacobian_core J m hm c hc hc0 hDc hroot hκ hr hrows

end PaperI.GaussHTransverseJacobian
