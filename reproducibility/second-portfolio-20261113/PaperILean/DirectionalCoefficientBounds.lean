import PaperILean.DirectionalCoefficientJets
import PaperILean.CompleteJetNormEquivalence

/-! Quantitative coefficient bounds for the directional class. The coefficient
norm is exactly the manuscript's fixed Euclidean monomial norm. The finite
constants depend only on k; M may vanish, and no invertibility is required.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem nonlinear_polynomial_coefficient_bound {k : ℕ} (F : CoefficientSpace k)
    (M : ℝ) (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F 0 1 r ≤ M)
    (e : Fin 3 →₀ ℕ) (he : 2 ≤ e.sum (fun _ n => n)) :
    |MvPolynomial.coeff e (coefficientPolynomial F)| ≤ M := by
  classical
  have hM0 := boundedJet_window_nonneg F 0 1 M hM
  by_cases hk : e.sum (fun _ n => n) ≤ k
  · let α : MonomialIndex k := (monomialIndexEquiv k).symm
        ⟨e, ⟨by omega, hk⟩⟩
    have hα : monomialExponent α = e :=
      congrArg Subtype.val ((monomialIndexEquiv k).apply_symm_apply ⟨e, ⟨by omega, hk⟩⟩)
    rw [← hα, coefficientPolynomial_coeff]
    have h := affineJet_nonlinear_coefficient_bound k 0 1 F M hM α
      (by rw [← sum_monomialExponent, hα]; exact he)
    simpa only [affineCoefficientMap_identity] using h
  · have hz : MvPolynomial.coeff e (coefficientPolynomial F) = 0 := by
      apply MvPolynomial.not_mem_support_iff.mp
      intro hn
      exact hk ((MvPolynomial.le_totalDegree hn).trans (coefficientPolynomial_totalDegree F))
    simpa only [hz, abs_zero] using hM0

theorem exponent_sum_add_single_one (e : Fin 3 →₀ ℕ) (i : Fin 3) :
    (e + Finsupp.single i 1).sum (fun _ n => n) = e.sum (fun _ n => n) + 1 := by
  classical
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype]
  · simp [Finsupp.add_apply, Finset.sum_add_distrib]
  · intro j; rfl
  · intro j; rfl

theorem abs_directionalCoefficient_le {k : ℕ} (F : CoefficientSpace k)
    (M : ℝ) (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F 0 1 r ≤ M)
    (u : PhysicalSpace) (α : MonomialIndex k) :
    |directionalCoefficientMap k u F α| ≤
      3 * ((k : ℝ) + 1) * physicalEuclideanNorm u * M := by
  have hM0 := boundedJet_window_nonneg F 0 1 M hM
  have hu0 := physicalEuclideanNorm_nonneg u
  rw [← coefficientPolynomial_coeff (directionalCoefficientMap k u F) α,
    coeff_directionalCoefficientMap u F _
    (monomialExponent_ne_zero α)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i : Fin 3, |u i * ((monomialExponent α i + 1 : ℕ) : ℝ) *
      MvPolynomial.coeff (monomialExponent α + Finsupp.single i 1)
        (coefficientPolynomial F)|) ≤
        ∑ _i : Fin 3, physicalEuclideanNorm u * ((k : ℝ) + 1) * M := by
      apply Finset.sum_le_sum
      intro i _
      have hu : |u i| ≤ physicalEuclideanNorm u := abs_le_sqrt_sum_sq u i
      have he : ((monomialExponent α i + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        have hi := (exponent_le_sum (monomialExponent α) i).trans
          (by simpa only [sum_monomialExponent] using α.property.2)
        exact_mod_cast Nat.add_le_add_right hi 1
      have hc := nonlinear_polynomial_coefficient_bound F M hM
        (monomialExponent α + Finsupp.single i 1)
        (by rw [exponent_sum_add_single_one, sum_monomialExponent]; have := α.property.1; omega)
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (show 0 ≤ ((monomialExponent α i + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
      gcongr
    _ = 3 * ((k : ℝ) + 1) * physicalEuclideanNorm u * M := by simp; ring

theorem coefficientEuclideanNorm_le_of_component_bound {k : ℕ}
    (F : CoefficientSpace k) (t : ℝ) (ht : 0 ≤ t) (hF : ∀ α, |F α| ≤ t) :
    coefficientEuclideanNorm F ≤ Real.sqrt (Fintype.card (MonomialIndex k) : ℝ) * t := by
  have hs : ∑ α, (F α) ^ 2 ≤ (Fintype.card (MonomialIndex k) : ℝ) * t ^ 2 := by
    calc
      ∑ α, (F α) ^ 2 ≤ ∑ _α : MonomialIndex k, t ^ 2 := by
        apply Finset.sum_le_sum
        intro α _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ht).mpr (hF α)
      _ = (Fintype.card (MonomialIndex k) : ℝ) * t ^ 2 := by simp
  unfold coefficientEuclideanNorm
  apply (Real.sqrt_le_sqrt hs).trans_eq
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

def directionalCoefficientConstant (k : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (MonomialIndex k) : ℝ) * (3 * ((k : ℝ) + 1))

theorem directionalCoefficientConstant_nonneg (k : ℕ) :
    0 ≤ directionalCoefficientConstant k := by unfold directionalCoefficientConstant; positivity

theorem directionalCoefficient_norm_bound {k : ℕ} (F : CoefficientSpace k)
    (M : ℝ) (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F 0 1 r ≤ M)
    (u : PhysicalSpace) :
    coefficientEuclideanNorm (directionalCoefficientMap k u F) ≤
      directionalCoefficientConstant k * M * physicalEuclideanNorm u := by
  have hM0 := boundedJet_window_nonneg F 0 1 M hM
  have hu0 := physicalEuclideanNorm_nonneg u
  have h := coefficientEuclideanNorm_le_of_component_bound
    (directionalCoefficientMap k u F) (3 * ((k : ℝ) + 1) * physicalEuclideanNorm u * M)
    (by positivity) (abs_directionalCoefficient_le F M hM u)
  exact h.trans_eq (by unfold directionalCoefficientConstant; ring)

theorem affineJetTensor_at_origin_identity {k : ℕ} (F : CoefficientSpace k) (r : ℕ) :
    affineJetTensor F 0 1 r = iteratedFDeriv ℝ r (phase F) 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [affineJetTensor_apply, Matrix.one_mulVec]

theorem jetTensorHSNorm_affine_coefficient_positive {k : ℕ}
    (F : CoefficientSpace k) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℕ) (hr : 0 < r) :
    jetTensorHSNorm (affineCoefficientMap k c B F) 0 1 r = jetTensorHSNorm F c B r := by
  rcases r with _ | n
  · omega
  · rw [← tensorHSNorm_affineJetTensor, affineJetTensor_at_origin_identity,
      iteratedFDeriv_phase_affine_positive, affinePoint_zero]
    exact tensorHSNorm_affineJetTensor F c B (n + 1)

theorem affine_directionalCoefficient_norm_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) (u : PhysicalSpace) :
    coefficientEuclideanNorm (directionalCoefficientMap k u (affineCoefficientMap k c B F)) ≤
      directionalCoefficientConstant k * M * physicalEuclideanNorm u := by
  apply directionalCoefficient_norm_bound
  convert hM using 1
  apply Finset.sum_congr rfl
  intro r hr
  exact jetTensorHSNorm_affine_coefficient_positive F c B r
    (by have := (Finset.mem_Icc.mp hr).1; omega)

theorem originJetTensor_sub_positive {k : ℕ} (F G : CoefficientSpace k)
    (r : ℕ) (hr : 0 < r) (hrk : r ≤ k) :
    affineJetTensor (F - G) 0 1 r = affineJetTensor F 0 1 r - affineJetTensor G 0 1 r := by
  rcases r with _ | n
  · omega
  · have hn : n < k := by omega
    have h := congrArg (fun T : CompleteSymmetricJets k => (T ⟨n, hn⟩).val)
      ((completeJetSymmetricMap k).map_sub F G)
    simp only [affineJetTensor_at_origin_identity]
    exact h

theorem jetTensorHSNorm_affine_coefficient_difference {k : ℕ}
    (F : CoefficientSpace k) (c c' : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℕ) (hr : 0 < r) (hrk : r ≤ k) :
    jetTensorHSNorm (affineCoefficientMap k c' B F - affineCoefficientMap k c B F) 0 1 r =
      jetTensorDifferenceHSNorm F c c' B r := by
  rw [← tensorHSNorm_affineJetTensor, originJetTensor_sub_positive _ _ r hr hrk]
  unfold jetTensorDifferenceHSNorm
  congr 1
  rcases r with _ | n
  · omega
  · simp only [affineJetTensor_at_origin_identity,
      iteratedFDeriv_phase_affine_positive, affinePoint_zero]
    rfl

theorem affine_directionalCoefficient_difference_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M)
    (h : PhysicalSpace) (hh : physicalEuclideanNorm h ≤ 1) (u : PhysicalSpace) :
    coefficientEuclideanNorm
      (directionalCoefficientMap k u (affineCoefficientMap k (c + B *ᵥ h) B F) -
        directionalCoefficientMap k u (affineCoefficientMap k c B F)) ≤
      directionalCoefficientConstant k * ((k : ℝ) ^ 2 * M * physicalEuclideanNorm h) *
        physicalEuclideanNorm u := by
  rw [← map_sub]
  apply directionalCoefficient_norm_bound
  have hb := boundedJet_center_variation_bound k F c B h M hM hh
  convert hb using 1
  apply Finset.sum_congr rfl
  intro r hr
  have hm := Finset.mem_Icc.mp hr
  exact jetTensorHSNorm_affine_coefficient_difference F c (c + B *ᵥ h) B r
    (by omega) hm.2

end PaperI
