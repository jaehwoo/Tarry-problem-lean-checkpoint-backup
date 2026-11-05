import PaperILean.CoefficientFrameBounds
import PaperILean.BoundedCenterLattice

/-! I546--549: recover the original nonconstant coefficient norm from every
positive raw jet at a bounded center. The proof uses the previously checked
finite Taylor transport, not a supplied inverse estimate. Degree zero and the
zero polynomial are included. Constants precede F and the center. -/
noncomputable section
open scoped BigOperators Matrix
namespace PaperI

def positiveJetHSum {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 k, jetTensorHSNorm F c B r

theorem positiveJetHSum_nonneg {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ positiveJetHSum F c B :=
  Finset.sum_nonneg (fun r _ => jetTensorHSNorm_nonneg F c B r)

theorem positiveJetHSNorm_le_sum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ)
    (hr : r ∈ Finset.Icc 1 k) : jetTensorHSNorm F c B r ≤ positiveJetHSum F c B :=
  Finset.single_le_sum (fun s _ => jetTensorHSNorm_nonneg F c B s) hr

theorem positiveJet_origin_bound {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (H : ℝ) (hH : 1 ≤ H) (hc : physicalEuclideanNorm c ≤ H)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 k) :
    jetTensorHSNorm F 0 1 r ≤ ((k : ℝ)+1)*H^k*positiveJetHSum F c 1 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hs0 := positiveJetHSum_nonneg F c 1
  have hh : physicalEuclideanNorm (-c) ≤ H := by
    simpa only [physicalEuclideanNorm, coordinateL2Norm_eq_norm, map_neg, norm_neg] using hc
  have hzero : c + (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (-c) = 0 := by simp
  rw [← tensorHSNorm_affineJetTensor, ← hzero, affineJetTensor_center_transport]
  apply (tensorHSNorm_sum_le _ _).trans
  calc
    _ ≤ ∑ _m ∈ Finset.range (k-r+1), H^k*positiveJetHSum F c 1 := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 := Finset.mem_range.mp hm
      have hr0 := Finset.mem_Icc.mp hr
      have hmK : m ≤ k := by omega
      have hrm : r+m ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [tensorHSNorm_smul, abs_of_nonneg (factorial_inv_nonneg _)]
      have ht := tensorHSNorm_contractRepeated_le m r (affineJetTensor F c 1 (r+m)) (-c)
      rw [tensorHSNorm_affineJetTensor] at ht
      have hp := (pow_le_pow_left₀ (physicalEuclideanNorm_nonneg (-c)) hh m).trans
        (pow_le_pow_right₀ hH hmK)
      have hval : 0 ≤ physicalEuclideanNorm (-c)^m * jetTensorHSNorm F c 1 (r+m) :=
        mul_nonneg (pow_nonneg (physicalEuclideanNorm_nonneg _) _)
          (jetTensorHSNorm_nonneg _ _ _ _)
      calc
        _ ≤ physicalEuclideanNorm (-c)^m * jetTensorHSNorm F c 1 (r+m) := by
          exact (mul_le_mul_of_nonneg_left ht (factorial_inv_nonneg _)).trans
            (by simpa using mul_le_mul_of_nonneg_right (factorial_inv_le_one m) hval)
        _ ≤ _ := mul_le_mul hp (positiveJetHSNorm_le_sum F c 1 (r+m) hrm)
          (jetTensorHSNorm_nonneg _ _ _ _) (pow_nonneg hH0 _)
    _ = (k-r+1 : ℕ) * (H^k*positiveJetHSum F c 1) := by simp
    _ ≤ ((k : ℝ)+1) * (H^k*positiveJetHSum F c 1) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg hH0 _) hs0)
      exact_mod_cast (show k-r+1 ≤ k+1 by omega)
    _ = _ := by ring

def inverseTaylorConstant (k : ℕ) (H : ℝ) : ℝ :=
  (Real.sqrt (Fintype.card (MonomialIndex k) : ℝ)+1) * (((k : ℝ)+1)*H^k)

theorem inverseTaylorConstant_pos (k : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    0 < inverseTaylorConstant k H := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  unfold inverseTaylorConstant
  positivity

theorem coefficientNorm_le_positiveJetHSum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (H : ℝ) (hH : 1 ≤ H) (hc : physicalEuclideanNorm c ≤ H) :
    coefficientEuclideanNorm F ≤ inverseTaylorConstant k H * positiveJetHSum F c 1 := by
  have ht : 0 ≤ ((k : ℝ)+1)*H^k*positiveJetHSum F c 1 := by
    apply mul_nonneg _ (positiveJetHSum_nonneg F c 1)
    exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hH) _)
  have hb : ∀ α, |F α| ≤ ((k : ℝ)+1)*H^k*positiveJetHSum F c 1 := by
    intro α
    have ha := affineJet_coefficient_le_HSNorm k 0 1 F (monomialExponent α)
      (monomialExponent_ne_zero α)
    rw [affineCoefficientMap_identity, coefficientPolynomial_coeff, sum_monomialExponent] at ha
    exact ha.trans (positiveJet_origin_bound F c H hH hc _
      (Finset.mem_Icc.mpr α.property))
  calc
    _ ≤ Real.sqrt (Fintype.card (MonomialIndex k) : ℝ) *
        (((k : ℝ)+1)*H^k*positiveJetHSum F c 1) :=
      coefficientEuclideanNorm_le_of_component_bound F _ ht hb
    _ ≤ (Real.sqrt (Fintype.card (MonomialIndex k) : ℝ)+1) *
        (((k : ℝ)+1)*H^k*positiveJetHSum F c 1) := by gcongr; linarith
    _ = _ := by unfold inverseTaylorConstant; ring

theorem bounded_center_inverseTaylor (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : CoefficientSpace k) (c : PhysicalSpace),
      c ∈ X → coefficientEuclideanNorm F ≤ C * positiveJetHSum F c 1 := by
  obtain ⟨T, _, hT⟩ := hX.exists_pos_norm_le
  let H' := max 1 (Real.sqrt 3*T)
  have hH' : 1 ≤ H' := le_max_left _ _
  refine ⟨inverseTaylorConstant k H', inverseTaylorConstant_pos k H' hH', ?_⟩
  intro F c hc
  exact coefficientNorm_le_positiveJetHSum F c H' hH'
    (((physicalEuclideanNorm_le_sqrt_three_piNorm c).trans
      (mul_le_mul_of_nonneg_left (hT c hc) (Real.sqrt_nonneg _))).trans (le_max_right _ _))

end PaperI
