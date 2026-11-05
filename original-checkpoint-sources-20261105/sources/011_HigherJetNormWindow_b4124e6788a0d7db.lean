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
  let r : Fin k := ⟨n - 1, by omega⟩
  have hr : r.val ≠ 0 := by dsimp [r]; omega
  have heq : r.val + 1 = n := by dsimp [r]; omega
  have h := congrArg Subtype.val
    (congrFun (completeJetSymmetricMap_higherJetCoefficientPart k F) r)
  simp only [higherSymmetricJetPart, if_neg hr] at h
  change iteratedFDeriv ℝ (r.val + 1) (phase (higherJetCoefficientPart k F)) 0 =
    iteratedFDeriv ℝ (r.val + 1) (phase F) 0 at h
  simpa only [heq] using h

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

end PaperI
