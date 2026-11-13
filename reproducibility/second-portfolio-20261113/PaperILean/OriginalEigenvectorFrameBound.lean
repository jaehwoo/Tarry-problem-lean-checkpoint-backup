import PaperILean.RawJetContractionBounds
import PaperILean.MinimizerTranslationStop

/-! Original proof route, manuscript I255-259.

Pre-strategy obstruction checks: the frame is positive definite, so its unit
Gram eigenvectors have positive eigenvalues. The logarithm is only used after
this fact. The endpoint d = 1 is permitted (log 1 = 0); repeated eigenvalues
need no choice of a simple spectrum, since the argument below applies to every
eigenvector. Degrees k = 0,1 give empty weighted sums and are retained. The
regularization is allowed to vanish; a negative regularization would invalidate
the sign step and is not claimed. The uniform constant is selected before R,
F,c,lambda,B,e,d, and depends only on k and the bounded source region X.

The declarations below evaluate the balance on an eigenvector. They do not use
minimizing_gram_dominance, minimizing_gram_quadratic_dominance, or any prior lower
frame bound as proof inputs.
-/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem original_log_mulVec_of_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e : Fin n → ℝ) (a : ℝ) (he : A *ᵥ e = a • e) :
    CFC.log A *ᵥ e = Real.log a • e := by
  let U := hA.isHermitian.eigenvectorUnitary
  let w := star (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ e
  have huw : (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ w = e := by
    rw [show w = star (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ e from rfl, Matrix.mulVec_mulVec,
      Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.one_mulVec]
  have hw : Matrix.diagonal hA.isHermitian.eigenvalues *ᵥ w = a • w := by
    have h := congrArg (fun v => star (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) he
    conv_lhs at h => rw [hA.isHermitian.spectral_theorem]
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc,
      U, unitary.coe_star_mul_self, one_mul, Matrix.mulVec_smul,
      RCLike.ofReal_real_eq_id, Function.id_comp, w] using h
  have hwlog : Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) *ᵥ w =
      Real.log a • w := by
    ext i
    have hi := congrFun hw i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hi ⊢
    by_cases hwi : w i = 0
    · simp [hwi]
    · rw [mul_right_cancel₀ hwi hi]
  rw [sourceMatrix_log_eq_spectral A hA]
  change ((U : Matrix (Fin n) (Fin n) ℝ) *
    Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) *
    star (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ e = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ
    (Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) *ᵥ w) = _
  rw [hwlog, Matrix.mulVec_smul, huw]

theorem original_unit_gram_eigenvector_physical_sq
    (B : Matrix (Fin 3) (Fin 3) ℝ) (e : PhysicalSpace) (d : ℝ)
    (he : physicalEuclideanNorm e = 1)
    (hEigen : (Bᵀ * B) *ᵥ e = (d ^ 2) • e) :
    (physicalEuclideanNorm (B *ᵥ e)) ^ 2 = d ^ 2 := by
  rw [← rightGram_quadratic, hEigen, dotProduct_smul, smul_eq_mul,
    ← physicalEuclideanNorm_sq_eq_dotProduct, he]
  ring

theorem original_minimizing_eigenvector_balance {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (e : PhysicalSpace) (d : ℝ) (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e) :
    1 - 2 * lam * Real.log (d ^ 2) =
      d ^ 2 + translationWeightedContractionSum F c B.val e := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => dotProduct e (A *ᵥ e))
    (frame_balance_of_minimum F c lam B hB)
  change dotProduct e ((B.valᵀ * B.val + weightedJetContractionGram F c B.val +
    (2 * lam) • CFC.log (B.valᵀ * B.val)) *ᵥ e) = dotProduct e ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ e) at h
  have hlog := original_log_mulVec_of_eigenvector _ (frame_rightGram_posDef B) e (d ^ 2) hEigen
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, hEigen, hlog, smul_eq_mul,
    weightedJetContractionGram_quadratic,
    ← physicalEuclideanNorm_sq_eq_dotProduct, he, one_pow, mul_one] at h
  linarith


theorem original_unit_gram_eigenvalue_pos
    (B : PositiveFrame) (e : PhysicalSpace) (d : ℝ)
    (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e) : 0 < d ^ 2 := by
  have he0 : e ≠ 0 := by
    intro hzero
    simp [hzero, physicalEuclideanNorm, coordinateL2Norm] at he
  have h := (frame_rightGram_posDef B).2 e he0
  simpa only [star_trivial, hEigen, dotProduct_smul, smul_eq_mul,
    ← physicalEuclideanNorm_sq_eq_dotProduct, he, one_pow, mul_one] using h

theorem original_minimizing_eigenvalue_le_one {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (e : PhysicalSpace) (d : ℝ) (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e) : d ^ 2 ≤ 1 := by
  have hbal := original_minimizing_eigenvector_balance F c lam B hB e d he hEigen
  have hsum : 0 ≤ translationWeightedContractionSum F c B.val e := by
    unfold translationWeightedContractionSum
    exact Finset.sum_nonneg fun n hn => mul_nonneg (by positivity) (sq_nonneg _)
  by_contra h
  have hd : 1 < d ^ 2 := lt_of_not_ge h
  have hlog : 0 ≤ 2 * lam * Real.log (d ^ 2) :=
    mul_nonneg (by positivity) (Real.log_nonneg hd.le)
  linarith

theorem original_minimizing_eigenvector_left_inequality {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (e : PhysicalSpace) (d : ℝ) (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e) :
    1 ≤ 1 - 2 * lam * Real.log (d ^ 2) := by
  have hlog : Real.log (d ^ 2) ≤ 0 := Real.log_nonpos (sq_nonneg d)
    (original_minimizing_eigenvalue_le_one F c lam hlam B hB e d he hEigen)
  have hm : 2 * lam * Real.log (d ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (by positivity) hlog
  linarith

/-- The displayed three-part estimate in I257, with the original order of
quantifiers and a constant independent of R,F,c,lambda,B,e,d. -/
theorem original_minimizing_eigenvector_uniform_chain
    (k : ℕ) (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ e : PhysicalSpace, physicalEuclideanNorm e = 1 → ∀ d : ℝ,
      (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e →
      (1 ≤ 1 - 2 * lam * Real.log (d ^ 2)) ∧
      (1 - 2 * lam * Real.log (d ^ 2) =
        d ^ 2 + translationWeightedContractionSum F c B.val e) ∧
      (d ^ 2 + translationWeightedContractionSum F c B.val e ≤ (1 + C * R ^ 2) * d ^ 2) := by
  obtain ⟨C, hC, hc⟩ := source_weightedContraction_uniform_bound k X hX
  refine ⟨C, hC, ?_⟩
  intro R hR F hF c hcx lam hlam B hB e he d hEigen
  refine ⟨original_minimizing_eigenvector_left_inequality F c lam hlam B hB e d he hEigen,
    original_minimizing_eigenvector_balance F c lam B hB e d he hEigen, ?_⟩
  have hraw := hc R hR F hF c hcx B.val
    (minimizing_euclideanFrameOperatorNorm_le_one F c lam hlam B hB) e
  rw [original_unit_gram_eigenvector_physical_sq B.val e d he hEigen] at hraw
  nlinarith only [hraw]

/-- The same source display with the literal sum over r=2,...,k. -/
theorem original_minimizing_eigenvector_uniform_chain_Icc
    (k : ℕ) (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ e : PhysicalSpace, physicalEuclideanNorm e = 1 → ∀ d : ℝ,
      (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e →
      (1 ≤ 1 - 2 * lam * Real.log (d ^ 2)) ∧
      (1 - 2 * lam * Real.log (d ^ 2) =
        d ^ 2 + ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (directionalContractionHSNorm F c B.val e (r - 2)) ^ 2) ∧
      (d ^ 2 + ∑ r ∈ Finset.Icc 2 k, (r : ℝ) * (directionalContractionHSNorm F c B.val e (r - 2)) ^ 2 ≤
        (1 + C * R ^ 2) * d ^ 2) := by
  simpa only [translationWeightedContractionSum_eq_Icc] using
    original_minimizing_eigenvector_uniform_chain k X hX

/-- The scalar conclusion of the original eigenvector calculation. -/
theorem original_minimizing_eigenvector_inverse_radius_bound
    (k : ℕ) (X : Set PhysicalSpace) (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ e : PhysicalSpace, physicalEuclideanNorm e = 1 → ∀ d : ℝ, 0 ≤ d →
      (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e → a / R ≤ d := by
  obtain ⟨C, hC, hc⟩ := original_minimizing_eigenvector_uniform_chain k X hX
  refine ⟨(Real.sqrt (1 + C))⁻¹, by positivity, ?_⟩
  intro R hR F hF c hcx lam hlam B hB e he d hd hEigen
  obtain ⟨hleft, hidentity, hright⟩ := hc R hR F hF c hcx lam hlam B hB e he d hEigen
  have hquad : 1 ≤ (1 + C * R ^ 2) * d ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 + C) := Real.sqrt_pos.mpr (by linarith)
  have hR0 : 0 < R := by linarith
  have hf : 1 + C * R ^ 2 ≤ (1 + C) * R ^ 2 := by nlinarith
  have hsq : 1 ≤ (Real.sqrt (1 + C) * R * d) ^ 2 := by
    calc
      1 ≤ (1 + C * R ^ 2) * d ^ 2 := hquad
      _ ≤ ((1 + C) * R ^ 2) * d ^ 2 := mul_le_mul_of_nonneg_right hf (sq_nonneg d)
      _ = (Real.sqrt (1 + C) * R * d) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + C)]
  have hlin : 1 ≤ Real.sqrt (1 + C) * R * d := by
    nlinarith [mul_nonneg (mul_nonneg hs.le hR0.le) hd]
  apply (div_le_iff₀ hR0).mpr
  have hdiv : (Real.sqrt (1 + C))⁻¹ * 1 ≤ d * R :=
    (inv_mul_le_iff₀ hs).mpr (by nlinarith only [hlin])
  simpa only [mul_one] using hdiv


/-- The elementary final spectral step, independent of the minimizing argument. -/
theorem original_rightGram_lower_of_eigenvalues (B : PositiveFrame)
    (b : ℝ) (hb : 0 ≤ b)
    (he : ∀ i : Fin 3, b ^ 2 ≤ (frame_rightGram_posDef B).isHermitian.eigenvalues i)
    (u : PhysicalSpace) : b * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u) := by
  let hA := frame_rightGram_posDef B
  have hp : (Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i - b ^ 2)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (he i))
  have h := orthogonalConjugate_posSemidef hA.isHermitian.eigenvectorUnitary _ hp
  have hs : orthogonalConjugate hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal hA.isHermitian.eigenvalues) = B.valᵀ * B.val := by
    simpa [orthogonalConjugate, Function.comp_def] using hA.isHermitian.spectral_theorem.symm
  have hd : Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i - b ^ 2) =
      Matrix.diagonal hA.isHermitian.eigenvalues - (b ^ 2) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hc : orthogonalConjugate hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal hA.isHermitian.eigenvalues - (b ^ 2) • 1) =
        B.valᵀ * B.val - (b ^ 2) • 1 := by
    rw [orthogonalConjugate]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, Matrix.mem_unitaryGroup_iff.mp hA.isHermitian.eigenvectorUnitary.property]
    change orthogonalConjugate hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal hA.isHermitian.eigenvalues) - (b ^ 2) • 1 = _
    rw [hs]
  rw [hd, hc] at h
  have hq := h.2 u
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    rightGram_quadratic, ← physicalEuclideanNorm_sq_eq_dotProduct] at hq
  nlinarith [physicalEuclideanNorm_nonneg (B.val *ᵥ u),
    mul_nonneg hb (physicalEuclideanNorm_nonneg u)]

/-- A replacement with exactly the all-directions interface used by the existing
mainstream audits, now obtained through the original unit-eigenvector display. -/
theorem original_minimizing_frame_lower_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ a : ℝ, 0 < a ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : PhysicalSpace, c ∈ X →
      ∀ lam : ℝ, 0 ≤ lam → ∀ B : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) →
      ∀ u : PhysicalSpace, a / R * physicalEuclideanNorm u ≤ physicalEuclideanNorm (B.val *ᵥ u) := by
  obtain ⟨a, ha, hbound⟩ := original_minimizing_eigenvector_inverse_radius_bound k X hX
  refine ⟨a, ha, ?_⟩
  intro R hR F hF c hc lam hlam B hB u
  apply original_rightGram_lower_of_eigenvalues B (a / R) (by positivity) ?_ u
  intro i
  let hA := frame_rightGram_posDef B
  let e : PhysicalSpace := hA.isHermitian.eigenvectorBasis i
  have he : physicalEuclideanNorm e = 1 := by
    rw [physicalEuclideanNorm, coordinateL2Norm_eq_norm]
    change ‖hA.isHermitian.eigenvectorBasis i‖ = 1
    exact hA.isHermitian.eigenvectorBasis.orthonormal.1 i
  have hs : (Real.sqrt (hA.isHermitian.eigenvalues i)) ^ 2 = hA.isHermitian.eigenvalues i :=
    Real.sq_sqrt (hA.eigenvalues_pos i).le
  have heig : (B.valᵀ * B.val) *ᵥ e =
      (Real.sqrt (hA.isHermitian.eigenvalues i)) ^ 2 • e := by
    rw [hs]
    exact hA.isHermitian.mulVec_eigenvectorBasis i
  have hi := hbound R hR F hF c hc lam hlam B hB e he
    (Real.sqrt (hA.isHermitian.eigenvalues i)) (Real.sqrt_nonneg _) heig
  have hsq := pow_le_pow_left₀ (show 0 ≤ a / R by positivity) hi 2
  simpa only [hs] using hsq


/-- Degree-zero and degree-one cases retain the empty sum literally. -/
theorem original_low_degree_contraction_sum_zero {k : ℕ} (hk : k ≤ 1)
    (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (e : PhysicalSpace) :
    translationWeightedContractionSum F c B e = 0 := by
  simp [translationWeightedContractionSum, Nat.sub_eq_zero_of_le hk]

theorem original_low_degree_minimizing_eigenvalue_eq_one {k : ℕ} (hk : k ≤ 1)
    (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (e : PhysicalSpace) (d : ℝ) (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = (d ^ 2) • e) : d ^ 2 = 1 := by
  have hi := original_minimizing_eigenvector_balance F c lam B hB e d he hEigen
  rw [original_low_degree_contraction_sum_zero hk, add_zero] at hi
  have hlo := original_minimizing_eigenvector_left_inequality F c lam hlam B hB e d he hEigen
  have hhi := original_minimizing_eigenvalue_le_one F c lam hlam B hB e d he hEigen
  linarith

theorem original_unit_eigenvalue_contraction_sum_zero {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (lam : ℝ) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (e : PhysicalSpace) (he : physicalEuclideanNorm e = 1)
    (hEigen : (B.valᵀ * B.val) *ᵥ e = e) :
    translationWeightedContractionSum F c B.val e = 0 := by
  have hi := original_minimizing_eigenvector_balance F c lam B hB e 1 he
    (by simpa only [one_pow, one_smul] using hEigen)
  simp only [one_pow, Real.log_one, mul_zero, sub_zero] at hi
  linarith

end PaperI
