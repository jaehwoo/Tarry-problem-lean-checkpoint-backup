import PaperILean.InverseTaylorRecovery
import PaperILean.RawJetUniformBounds
import PaperILean.OriginalUpperNormalPullback

/-! I897/I1305: polynomial pullback bounds for the complete original
nonconstant coefficient vector. The constants precede both radii and all
phases/frames. Translation is retained; no invertibility is used. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

theorem originalPositiveJet_polynomial_center_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (H : ℝ) (hH : 1 ≤ H) (hc : physicalEuclideanNorm c ≤ H)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 k) :
    jetTensorHSNorm F c 1 r ≤ ((k : ℝ)+1)*H^k*positiveJetHSum F 0 1 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hs0 := positiveJetHSum_nonneg F 0 1
  have hpoint : (0 : PhysicalSpace) + (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ c = c := by simp
  rw [← tensorHSNorm_affineJetTensor, ← hpoint, affineJetTensor_center_transport]
  apply (tensorHSNorm_sum_le _ _).trans
  calc
    _ ≤ ∑ _m ∈ Finset.range (k-r+1), H^k*positiveJetHSum F 0 1 := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 := Finset.mem_range.mp hm
      have hr0 := Finset.mem_Icc.mp hr
      have hmK : m ≤ k := by omega
      have hrm : r+m ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [tensorHSNorm_smul, abs_of_nonneg (factorial_inv_nonneg _)]
      have ht := tensorHSNorm_contractRepeated_le m r (affineJetTensor F 0 1 (r+m)) c
      rw [tensorHSNorm_affineJetTensor] at ht
      have hp := (pow_le_pow_left₀ (physicalEuclideanNorm_nonneg c) hc m).trans
        (pow_le_pow_right₀ hH hmK)
      calc
        _ ≤ tensorHSNorm (tensorContractRepeated m r (affineJetTensor F 0 1 (r+m)) c) :=
          mul_le_of_le_one_left (tensorHSNorm_nonneg _) (factorial_inv_le_one _)
        _ ≤ _ := ht.trans (mul_le_mul hp (positiveJetHSNorm_le_sum F 0 1 (r+m) hrm)
          (jetTensorHSNorm_nonneg _ _ _ _) (pow_nonneg hH0 _))
    _ = (k-r+1 : ℕ) * (H^k*positiveJetHSum F 0 1) := by simp
    _ ≤ ((k : ℝ)+1) * (H^k*positiveJetHSum F 0 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show k-r+1 ≤ k+1 by omega))
        (mul_nonneg (pow_nonneg hH0 _) hs0)
    _ = _ := by ring

theorem originalPositiveJet_origin_coefficient_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ F : CoefficientSpace k,
      positiveJetHSum F 0 1 ≤ C * coefficientEuclideanNorm F := by
  obtain ⟨D,hD,hbound⟩ := rawJetHSNorm_uniform_bound k {0} (isCompact_singleton.isBounded)
  refine ⟨((k : ℝ)+1)*D, one_le_mul_of_one_le_of_one_le (by have := (show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k); linarith) hD, ?_⟩
  intro F
  have hn : 0 ≤ coefficientEuclideanNorm F := Real.sqrt_nonneg _
  calc
    positiveJetHSum F 0 1 ≤ ∑ _r ∈ Finset.Icc 1 k, D * coefficientEuclideanNorm F := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← tensorHSNorm_affineJetTensor,affineJetTensor_at_origin_identity]
      exact hbound F 0 (Set.mem_singleton 0) r (Finset.mem_Icc.mp hr).2
    _ = (k : ℝ) * (D * coefficientEuclideanNorm F) := by simp
    _ ≤ ((k : ℝ)+1)*D*coefficientEuclideanNorm F := by nlinarith

theorem originalAffineCoefficient_polynomial_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H L : ℝ), 1 ≤ H → 1 ≤ L →
      ∀ (F : CoefficientSpace k) (c : PhysicalSpace) (A : Matrix (Fin 3) (Fin 3) ℝ),
      physicalEuclideanNorm c ≤ H → (∀ i j, |A i j| ≤ L) →
      coefficientEuclideanNorm (affineCoefficientMap k c A F) ≤
        C * H^k * L^k * coefficientEuclideanNorm F := by
  obtain ⟨D,hD,hbound⟩ := originalPositiveJet_origin_coefficient_bound k
  let C := (Real.sqrt (Fintype.card (MonomialIndex k) : ℝ)+1) * (9:ℝ)^k * ((k:ℝ)+1)*D
  have hC : 1 ≤ C := by
    apply one_le_mul_of_one_le_of_one_le _ hD
    apply one_le_mul_of_one_le_of_one_le _ (by have := (show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k); linarith)
    exact one_le_mul_of_one_le_of_one_le (by have := Real.sqrt_nonneg (Fintype.card (MonomialIndex k) : ℝ); linarith) (one_le_pow₀ (by norm_num))
  refine ⟨C,hC,?_⟩
  intro H L hH hL F c A hc hA
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hF0 : 0 ≤ coefficientEuclideanNorm F := Real.sqrt_nonneg _
  have hp0 : 0 ≤ (9*L)^k := pow_nonneg (by positivity) _
  have hb : ∀ α, |affineCoefficientMap k c A F α| ≤
      (9*L)^k * (((k:ℝ)+1)*H^k*(D*coefficientEuclideanNorm F)) := by
    intro α
    have ha := affineJet_coefficient_le_HSNorm k c A F (monomialExponent α)
      (monomialExponent_ne_zero α)
    rw [coefficientPolynomial_coeff,sum_monomialExponent] at ha
    have ht := tensorHSNorm_frame_bound (affineJetTensor F c 1 (totalDegree α.val)) A L hL0 hA
    rw [← affineJetTensor_right_frame,one_mul,tensorHSNorm_affineJetTensor,
      tensorHSNorm_affineJetTensor] at ht
    have hb := originalPositiveJet_polynomial_center_bound F c H hH hc _
      (Finset.mem_Icc.mpr α.property)
    have hp : (9*L)^(totalDegree α.val) ≤ (9*L)^k :=
      pow_le_pow_right₀ (by linarith) α.property.2
    apply ha.trans (ht.trans _)
    exact mul_le_mul hp (hb.trans (mul_le_mul_of_nonneg_left (hbound F) (by positivity)))
      (jetTensorHSNorm_nonneg _ _ _ _) hp0
  have hh := coefficientEuclideanNorm_le_of_component_bound (affineCoefficientMap k c A F)
    _ (by positivity) hb
  apply hh.trans
  calc
    _ ≤ (Real.sqrt (Fintype.card (MonomialIndex k) : ℝ)+1) *
        ((9*L)^k * (((k:ℝ)+1)*H^k*(D*coefficientEuclideanNorm F))) := by gcongr; linarith
    _ = _ := by dsimp [C]; rw [mul_pow]; ring

theorem originalAffineCoefficient_perturbation_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H L : ℝ), 1 ≤ H → 1 ≤ L →
      ∀ (F G : CoefficientSpace k) (c : PhysicalSpace) (A : Matrix (Fin 3) (Fin 3) ℝ),
      physicalEuclideanNorm c ≤ H → (∀ i j, |A i j| ≤ L) →
      coefficientEuclideanNorm (affineCoefficientMap k c A F - affineCoefficientMap k c A G) ≤
        C * H^k * L^k * coefficientEuclideanNorm (F-G) := by
  obtain ⟨C,hC,hbound⟩ := originalAffineCoefficient_polynomial_bound k
  refine ⟨C,hC,?_⟩
  intro H L hH hL F G c A hc hA
  rw [← map_sub]
  exact hbound H L hH hL (F-G) c A hc hA

end PaperI
