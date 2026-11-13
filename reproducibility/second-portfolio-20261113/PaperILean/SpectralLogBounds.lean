import PaperILean.MinimizerLowerBounds

/-! I259: spectral logarithm estimates for the actual CFC logarithm.
The Euclidean matrix norm bridge is proved explicitly; no entrywise logarithm,
Pi matrix norm, simple-spectrum assumption or lower bound hypothesis is hidden.
-/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem euclideanFrameMap_eq_toEuclideanCLM (A : Matrix (Fin 3) (Fin 3) ℝ) :
    euclideanFrameMap A = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (WithLp.linearEquiv 2 ℝ PhysicalSpace).symm.surjective x
  rw [euclideanFrameMap_apply]
  rfl

theorem euclideanFrameOperatorNorm_eq_l2_opNorm (A : Matrix (Fin 3) (Fin 3) ℝ) :
    euclideanFrameOperatorNorm A = ‖A‖ := by
  rw [euclideanFrameOperatorNorm, euclideanFrameMap_eq_toEuclideanCLM, Matrix.cstar_norm_def]

theorem euclidean_diagonal_norm_le (v : Fin 3 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i, |v i| ≤ M) : euclideanFrameOperatorNorm (Matrix.diagonal v) ≤ M := by
  apply (euclideanFrameOperatorNorm_le_iff _ M hM).mpr
  intro u
  have hs : (physicalEuclideanNorm (Matrix.diagonal v *ᵥ u)) ^ 2 ≤
      (M * physicalEuclideanNorm u) ^ 2 := by
    simp only [physicalEuclideanNorm, mul_pow, coordinateL2Norm_sq, Matrix.mulVec_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hsq : (v i) ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (u i))
  exact (sq_le_sq₀ (physicalEuclideanNorm_nonneg _) (mul_nonneg hM (physicalEuclideanNorm_nonneg u))).mp hs

theorem euclidean_orthogonalConjugate_norm (U : unitary (Matrix (Fin 3) (Fin 3) ℝ))
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    euclideanFrameOperatorNorm (orthogonalConjugate U A) = euclideanFrameOperatorNorm A := by
  simp only [euclideanFrameOperatorNorm_eq_l2_opNorm, orthogonalConjugate,
    ← unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem rightGram_eigenvalue_lower_of_direction_bound (B : PositiveFrame)
    (d : ℝ) (hd : 0 ≤ d)
    (hB : ∀ u : PhysicalSpace, d * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u))
    (i : Fin 3) : d ^ 2 ≤ (frame_rightGram_posDef B).isHermitian.eigenvalues i := by
  let hA := frame_rightGram_posDef B
  let v : PhysicalSpace := (hA.isHermitian.eigenvectorBasis i)
  have hv : physicalEuclideanNorm v = 1 := by
    rw [physicalEuclideanNorm, coordinateL2Norm_eq_norm]
    change ‖hA.isHermitian.eigenvectorBasis i‖ = 1
    exact hA.isHermitian.eigenvectorBasis.orthonormal.1 i
  have he : hA.isHermitian.eigenvalues i = (physicalEuclideanNorm (B.val *ᵥ v)) ^ 2 := by
    rw [hA.isHermitian.eigenvalues_eq]
    simpa only [star_trivial] using rightGram_quadratic B.val v
  have h := hB v
  rw [hv, mul_one] at h
  change d ^ 2 ≤ hA.isHermitian.eigenvalues i
  rw [he]
  exact pow_le_pow_left₀ hd h 2

theorem sourceMatrix_log_norm_le_of_eigenvalue_bounds
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) (M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i, |Real.log (hA.isHermitian.eigenvalues i)| ≤ M) :
    euclideanFrameOperatorNorm (CFC.log A) ≤ M := by
  rw [sourceMatrix_log_eq_spectral A hA]
  change euclideanFrameOperatorNorm (orthogonalConjugate hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)))) ≤ M
  rw [euclidean_orthogonalConjugate_norm]
  exact euclidean_diagonal_norm_le _ M hM he

theorem sourceMatrix_abs_trace_log_le_of_eigenvalue_bounds
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) (M : ℝ)
    (he : ∀ i, |Real.log (hA.isHermitian.eigenvalues i)| ≤ M) :
    |Matrix.trace (CFC.log A)| ≤ 3 * M := by
  rw [sourceMatrix_log_eq_spectral A hA]
  change |Matrix.trace (orthogonalConjugate hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i))))| ≤ 3 * M
  rw [trace_orthogonalConjugate, Matrix.trace_diagonal]
  calc
    _ ≤ ∑ i : Fin 3, |Real.log (hA.isHermitian.eigenvalues i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum (fun i _ => he i)
    _ = 3 * M := by simp

theorem scalar_log_bound_of_inverse_radius_interval (a CX : ℝ)
    (ha : 0 < a) (hCX : 2 ≤ CX) :
    ∃ C : ℝ, 0 < C ∧ ∀ R x : ℝ, 2 ≤ R → 0 < x → (a / R) ^ 2 ≤ x → x ≤ 1 →
      |Real.log x| ≤ C * sourceLogScale CX R := by
  let L0 := sourceLogScale CX 2
  have hL0 : 0 < L0 := sourceLogScale_pos CX 2 hCX (by norm_num)
  let C : ℝ := 2 + 2 * |Real.log a| / L0
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R x hR hx hlow hupp
  have hR0 : 0 < R := by linarith
  have hlog := Real.log_le_log (sq_pos_of_pos (div_pos ha hR0)) hlow
  rw [Real.log_pow, Real.log_div ha.ne' hR0.ne'] at hlog
  have hRlog : Real.log R ≤ sourceLogScale CX R := by
    apply Real.log_le_log hR0
    nlinarith
  have hL : L0 ≤ sourceLogScale CX R := sourceLogScale_monotone_from_two CX R hCX hR
  have hscale := mul_le_mul_of_nonneg_left hL (div_nonneg (abs_nonneg (Real.log a)) hL0.le)
  have hc : |Real.log a| / L0 * L0 = |Real.log a| := div_mul_cancel₀ _ hL0.ne'
  rw [hc] at hscale
  rw [abs_of_nonpos (Real.log_nonpos hx.le hupp)]
  have hneg := neg_abs_le (Real.log a)
  dsimp [C]
  rw [mul_div_assoc]
  push_cast at hlog
  nlinarith

end PaperI
