import PaperILean.OriginalNullPhysicalPivot
import PaperILean.NullGraphTransverseJacobian

/-! I3355[239,444) and its statement I3350[345,581): the original H0 null pivot.
The selected four rows are raw derivatives, including Dxzz = 2 times the
xz² coefficient. The H0 columns are the actual physical order (A,C,Tx,D).
No quantitative least-singular-value assertion is made here. -/

noncomputable section
namespace PaperI.OriginalNullPivot

open Filter PaperI.NormalFibers PaperI.NullGraphRawConstraints
  PaperI.NullGraphTransverseJacobian PaperI.OriginalNullPhysicalPivot
open scoped Topology

/-- The actual original phase-only H0 differential followed by four raw jet rows. -/
def rawH0Matrix {k : ℕ} (J : CoefficientSpace k) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' ((rawRowCLM k).toLinearMap.comp
    ((originalHaarPhysicalLieLinear J).comp (originalHaarLieEmbedLinear .H0)))

theorem rawH0Matrix_apply {k : ℕ} (J : CoefficientSpace k) (i j : Fin 4) :
    rawH0Matrix J i j =
      rawRowCLM k (originalHaarPhysicalLieAction J
        (originalHaarLieEmbed .H0 (Pi.single j 1))) i := by
  rw [rawH0Matrix, LinearMap.toMatrix'_apply]
  have he : (fun j' : Fin 4 => if j' = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext q
    by_cases hq : q = j
    · subst q; simp
    · simp [hq, Pi.single_eq_of_ne hq]
  rw [he]
  rfl

theorem rawH0Matrix_mulVec {k : ℕ} (J : CoefficientSpace k)
    (v : OriginalHaarLieCoordinates .H0) :
    (rawH0Matrix J).mulVec v =
      rawRowCLM k (originalHaarPhysicalLieAction J (originalHaarLieEmbed .H0 v)) := by
  exact congrArg (fun L : (Fin 4 → ℝ) →ₗ[ℝ] FrameSpace => L v)
    (Matrix.toLin'_toMatrix' ((rawRowCLM k).toLinearMap.comp
      ((originalHaarPhysicalLieLinear J).comp (originalHaarLieEmbedLinear .H0))))

/-- H0's (A,C,Tx,D) basis in the saved frame order (Tx,A,C,D). -/
noncomputable def h0ColumnPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

theorem h0ColumnPermutation_sign : Equiv.Perm.sign h0ColumnPermutation = 1 := by
  simp [h0ColumnPermutation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap]

/-- Exact matrix bridge, rather than assuming a desired determinant of the physical action. -/
theorem rawH0Matrix_eq_rawJacobian {k : ℕ} (J : CoefficientSpace k) :
    rawH0Matrix J = (ordinaryJacobian (bracketedRawNullConstraints J 2) 0).submatrix
      id h0ColumnPermutation := by
  ext i j
  rw [rawH0Matrix_apply]
  change _ = fderiv ℝ (bracketedRawNullConstraints J 2) 0
    (Pi.single (h0ColumnPermutation j) 1) i
  rw [raw_derivative_physical]
  have he : originalHaarLieEmbed .H0 (Pi.single j 1) =
      frameLieEmbed (Pi.single (h0ColumnPermutation j) 1) := by
    fin_cases j <;> ext q <;> fin_cases q <;>
      simp [h0ColumnPermutation, frameLieEmbed_apply, originalHaarLieEmbed,
        Pi.single_apply, Equiv.swap_apply_def]
  exact congrArg (fun v => rawRowCLM k (originalHaarPhysicalLieAction J v) i) he

theorem rawH0Matrix_det_eq_rawJacobian {k : ℕ} (J : CoefficientSpace k) :
    (rawH0Matrix J).det =
      (ordinaryJacobian (bracketedRawNullConstraints J 2) 0).det := by
  rw [rawH0Matrix_eq_rawJacobian, Matrix.det_permute', h0ColumnPermutation_sign]
  simp

private theorem pullback_origin (G : Poly) : pullback (0 : FrameSpace) 0 0 G = G := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => fin_cases i <;> simp [hP, frameVariables]

/-- The same graph gives the ordinary m=2 raw determinant, with no k>=4 restriction. -/
theorem ordinary_null_raw_determinant {k : ℕ} (J : CoefficientSpace k)
    (c : (Fin 2 → ℝ) → ℝ) (hc : ContinuousAt c 0) (hc0 : c 0 = 0)
    (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J 1 ![c v, v 0, v 1] = 0)
    (hLam : originalNormalPhase J 2 0 ≠ 0) (hB : mixedGraphDerivative c ≠ 0)
    (hconstraints : bracketedRawNullConstraints J 2 0 = 0) :
    (ordinaryJacobian (bracketedRawNullConstraints J 2) 0).det =
      -2 * (originalNormalPhase J 2 0) ^ 4 * mixedGraphDerivative c := by
  have hmix := graph_mixed_derivative J 1 c hc hc0 hDc hroot hLam
  let G := originalNormalPolynomial J 1
  have hpull : pullback (0 : FrameSpace) 0 0 G = G := pullback_origin G
  have hx : MvPolynomial.eval 0 (MvPolynomial.pderiv 0 G) = originalNormalPhase J 2 0 := by
    rw [← originalNormalPolynomial_succ, ← originalNormalPhase_eq_eval]
  have hrows : normalizationEquationsII G 0 0 0 = 0 := by
    simpa only [bracketedRawNullConstraints_eq J 2 (by omega)] using hconstraints
  have h0 : MvPolynomial.eval 0 G = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 0
  have hy : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 G) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 1
  have hz : MvPolynomial.eval 0 (MvPolynomial.pderiv 2 G) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 2
  have hzz : MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 G)) = 0 := by
    simpa [normalizationEquationsII, hpull] using congrFun hrows 3
  have hmixne : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 G)) ≠ 0 := by
    rw [hmix]
    exact mul_ne_zero (neg_ne_zero.mpr hLam) hB
  have hframe : (0 : FrameSpace) ∈ normalizedFrames G 0 0 := by
    change _ = 0 ∧ _ ≠ 0 ∧ _ = 0 ∧ _ = 0 ∧ ((_ = 0 ∧ _ ≠ 0) ∨ (_ = 0 ∧ _ ≠ 0))
    simp only [hpull]
    exact ⟨h0, by rwa [hx], hy, hz, Or.inr ⟨hzz, hmixne⟩⟩
  have hsigned := signed_jacobian_chartII G 0 0 0 hframe
  rw [hpull, hx, hmix] at hsigned
  rw [bracketedRawNullConstraints_eq J 2 (by omega)]
  exact hsigned.trans (by ring)

/-- The original physical H0 map is injective when its selected raw minor is nonzero. -/
theorem physical_h0_injective_of_minor {k : ℕ} (J : CoefficientSpace k)
    (hdet : (rawH0Matrix J).det ≠ 0) :
    Function.Injective (fun v : OriginalHaarLieCoordinates .H0 =>
      originalHaarPhysicalLieAction J (originalHaarLieEmbed .H0 v)) := by
  have hi : Function.Injective (rawH0Matrix J).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((rawH0Matrix J).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  intro u v huv
  apply hi
  rw [rawH0Matrix_mulVec, rawH0Matrix_mulVec]
  exact congrArg (rawRowCLM k) huv

/-- Complete original-null-pivot identification, retaining the same original phase and graph.
This is one manuscript stage printed at both I3355[239,444) and I3350[345,581).
The quantitative subgroup pivot used by the Haar theorem remains a separate hypothesis there. -/
theorem original_null_pivot_stage {k : ℕ} (J : CoefficientSpace k)
    (c : (Fin 2 → ℝ) → ℝ) (hc : ContinuousAt c 0) (hc0 : c 0 = 0)
    (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0, originalNormalPhase J 1 ![c v, v 0, v 1] = 0)
    (hLam : originalNormalPhase J 2 0 ≠ 0) (hB : mixedGraphDerivative c ≠ 0)
    (hconstraints : bracketedRawNullConstraints J 2 0 = 0) :
    (rawH0Matrix J).det = -2 * (originalNormalPhase J 2 0) ^ 4 * mixedGraphDerivative c ∧
      |(rawH0Matrix J).det| = 2 * |originalNormalPhase J 2 0| ^ 4 * |mixedGraphDerivative c| ∧
      Function.Injective (fun v : OriginalHaarLieCoordinates .H0 =>
        originalHaarPhysicalLieAction J (originalHaarLieEmbed .H0 v)) := by
  have hd : (rawH0Matrix J).det =
      -2 * (originalNormalPhase J 2 0) ^ 4 * mixedGraphDerivative c := by
    rw [rawH0Matrix_det_eq_rawJacobian]
    exact ordinary_null_raw_determinant J c hc hc0 hDc hroot hLam hB hconstraints
  refine ⟨hd, ?_, physical_h0_injective_of_minor J ?_⟩
  · rw [hd, abs_mul, abs_mul, abs_pow]
    norm_num
  · rw [hd]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hLam)) hB

end PaperI.OriginalNullPivot
