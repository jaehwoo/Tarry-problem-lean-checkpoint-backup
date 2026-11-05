import PaperILean.CompleteJetNormEquivalence
import PaperILean.JetWindowVolume

/-! The nonlinear coefficient window by the original symmetric-tensor norm route.

The first tensor is removed before applying complete-jet norm equivalence, so
its bound K does not enter the radius of the higher coefficients. This retains
exactly three growing linear coordinates in the subsequent volume argument.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PaperI

/-- Retain precisely the tensors of orders 2 through k. -/
def higherSymmetricJetPart (k : ℕ) (T : CompleteSymmetricJets k) :
    CompleteSymmetricJets k := fun r => if r.val = 0 then 0 else T r

/-- Reconstruct the coefficient vector after removing the first tensor. -/
def higherJetCoefficientPart (k : ℕ) (F : CoefficientSpace k) : CoefficientSpace k :=
  symmetricJetCoefficientMap k (higherSymmetricJetPart k (completeJetSymmetricMap k F))

theorem completeJetSymmetricMap_higherJetCoefficientPart (k : ℕ)
    (F : CoefficientSpace k) :
    completeJetSymmetricMap k (higherJetCoefficientPart k F) =
      higherSymmetricJetPart k (completeJetSymmetricMap k F) :=
  symmetricJetCoefficientMap_right_inverse k _

theorem iteratedFDeriv_higherJetCoefficientPart (k : ℕ) (F : CoefficientSpace k)
    (n : ℕ) (hn : 2 ≤ n) (hnk : n ≤ k) :
    iteratedFDeriv ℝ n (phase (higherJetCoefficientPart k F)) 0 =
      iteratedFDeriv ℝ n (phase F) 0 := by
  cases n with
  | zero => omega
  | succ n =>
    let r : Fin k := ⟨n, by omega⟩
    have hr : r.val ≠ 0 := by dsimp [r]; omega
    have h := congrArg Subtype.val
      (congrFun (completeJetSymmetricMap_higherJetCoefficientPart k F) r)
    simp only [higherSymmetricJetPart, if_neg hr] at h
    exact h

theorem higherJetCoefficientPart_eq_of_degree_ge_two (k : ℕ)
    (F : CoefficientSpace k) (α : MonomialIndex k) (hα : 2 ≤ totalDegree α.val) :
    higherJetCoefficientPart k F α = F α := by
  have hlen : (coordinateDerivativeOrder (monomialExponent α)).length =
      totalDegree α.val := by rw [coordinateDerivativeOrder_length, sum_monomialExponent]
  have h := congrArg (fun T : TensorSpace
      (coordinateDerivativeOrder (monomialExponent α)).length =>
      T (fun j => Pi.single ((coordinateDerivativeOrder (monomialExponent α)).get j) (1 : ℝ)))
    (iteratedFDeriv_higherJetCoefficientPart k F _
      (by rw [hlen]; exact hα) (by rw [hlen]; exact α.property.2))
  dsimp only at h
  rw [iteratedFDeriv_phase_mixed_zero, iteratedFDeriv_phase_mixed_zero,
    coefficientPolynomial_coeff, coefficientPolynomial_coeff] at h
  have hpos := coordinateFactorialProduct_one_le (monomialExponent α)
  nlinarith

theorem jetTensorHSNorm_higherJetCoefficientPart (k : ℕ)
    (F : CoefficientSpace k) (r : Fin k) :
    jetTensorHSNorm (higherJetCoefficientPart k F) 0 1 (r.val + 1) =
      if r.val = 0 then 0 else jetTensorHSNorm F 0 1 (r.val + 1) := by
  have h := congrArg Subtype.val
    (congrFun (completeJetSymmetricMap_higherJetCoefficientPart k F) r)
  by_cases hr : r.val = 0
  · simp only [higherSymmetricJetPart, if_pos hr] at h
    change iteratedFDeriv ℝ (r.val + 1) (phase (higherJetCoefficientPart k F)) 0 = 0 at h
    simp [jetTensorHSNorm, jetTensorComponent, h, hr]
  · simp only [higherSymmetricJetPart, if_neg hr] at h
    change iteratedFDeriv ℝ (r.val + 1) (phase (higherJetCoefficientPart k F)) 0 =
      iteratedFDeriv ℝ (r.val + 1) (phase F) 0 at h
    simp only [if_neg hr, jetTensorHSNorm, jetTensorComponent, h]

theorem jetTensorHSNorm_affine_positive (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (r : ℕ) :
    jetTensorHSNorm (affineCoefficientMap k c B F) 0 1 (r + 1) =
      jetTensorHSNorm F c B (r + 1) := by
  unfold jetTensorHSNorm jetTensorComponent
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.one_mulVec]
  rw [iteratedFDeriv_phase_affine_zero_positive]

/-- After removing the first tensor, the complete HS norm is bounded solely by
k and the higher-tensor budget; no linear-jet bound is used. -/
theorem completeJetHSNorm_higher_affine_bound (k : ℕ) (F : CoefficientSpace k)
    (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ) (M : ℝ)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) :
    completeJetHSNorm (higherJetCoefficientPart k (affineCoefficientMap k c B F)) 0 1 ≤
      ((k : ℝ) + 1) * higherJetRadius M := by
  let H := higherJetCoefficientPart k (affineCoefficientMap k c B F)
  have hR := higherJetRadius_nonneg M
  have heach (r : Fin k) : jetTensorHSNorm H 0 1 (r.val + 1) ≤ higherJetRadius M := by
    dsimp [H]
    rw [jetTensorHSNorm_higherJetCoefficientPart]
    split_ifs with hr
    · exact hR
    · rw [jetTensorHSNorm_affine_positive]
      have hmem : r.val + 1 ∈ Finset.Icc 2 k := by
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      exact (Finset.single_le_sum (fun n _ => jetTensorHSNorm_nonneg F c B n) hmem).trans
        (hM.trans (le_higherJetRadius M))
  change Real.sqrt (∑ r : Fin k, (jetTensorHSNorm H 0 1 (r.val + 1)) ^ 2) ≤ _
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs : ∑ r : Fin k, (jetTensorHSNorm H 0 1 (r.val + 1)) ^ 2 ≤
        (k : ℝ) * (higherJetRadius M) ^ 2 := by
      calc
        _ ≤ ∑ _r : Fin k, (higherJetRadius M)^2 := by
          apply Finset.sum_le_sum
          intro r _
          exact pow_le_pow_left₀ (jetTensorHSNorm_nonneg H 0 1 _) (heach r) 2
        _ = _ := by simp
    have hk : (k : ℝ) ≤ ((k : ℝ) + 1)^2 := by
      nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
    calc
      _ ≤ (k : ℝ) * (higherJetRadius M)^2 := hs
      _ ≤ ((k : ℝ) + 1)^2 * (higherJetRadius M)^2 :=
        mul_le_mul_of_nonneg_right hk (sq_nonneg _)
      _ = (((k : ℝ) + 1) * higherJetRadius M)^2 := by ring

/-- Original norm-equivalence boundedness of all higher normalized coefficients.
The radius is chosen before the center, frame, phase, and linear budget. -/
theorem exists_higherJet_coefficient_radius (k : ℕ) (M : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
      (F : CoefficientSpace k),
      (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ M) →
      ∀ α : MonomialIndex k, 2 ≤ totalDegree α.val →
        |affineCoefficientMap k c B F α| ≤ R := by
  obtain ⟨C, hC, hnorm⟩ := completeJet_norm_equivalence k
  have hCpos : 0 < C := by linarith
  refine ⟨C * (((k : ℝ) + 1) * higherJetRadius M), by
    have := higherJetRadius_nonneg M
    positivity, ?_⟩
  intro c B F hM α hα
  let H := higherJetCoefficientPart k (affineCoefficientMap k c B F)
  have hcoef : |affineCoefficientMap k c B F α| ≤ coefficientEuclideanNorm H := by
    rw [← higherJetCoefficientPart_eq_of_degree_ge_two k _ α hα]
    exact abs_le_sqrt_sum_sq H α
  have hnormH : coefficientEuclideanNorm H ≤ C * completeJetHSNorm H 0 1 := by
    exact (inv_mul_le_iff₀ hCpos).mp (hnorm H).1
  exact hcoef.trans (hnormH.trans (mul_le_mul_of_nonneg_left
    (completeJetHSNorm_higher_affine_bound k F c B M hM) hCpos.le))

end PaperI
