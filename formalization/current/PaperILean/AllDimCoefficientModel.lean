import PaperILean.AllDimCoefficientSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Linarith

/-! Complete nonconstant monomial coefficients, with no degree restriction
beyond the manuscript's total-degree condition. -/

open scoped BigOperators

noncomputable section
namespace PaperI.AllDim

variable {n : ℕ}

def monomialExponent {n k : ℕ} (α : MonomialIndex n k) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.val i).val)

@[simp] theorem monomialExponent_apply {n k : ℕ} (α : MonomialIndex n k) (i : Fin n) :
    monomialExponent α i = (α.val i).val := rfl

theorem sum_monomialExponent {n k : ℕ} (α : MonomialIndex n k) :
    (monomialExponent α).sum (fun _ e => e) = totalDegree α.val := by
  rw [Finsupp.sum_fintype]
  · rfl
  · intro i
    rfl

theorem exponent_le_sum (e : Fin n →₀ ℕ) (i : Fin n) :
    e i ≤ e.sum (fun _ n => n) := by
  rw [Finsupp.sum_fintype]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · intro i
    rfl

def nonconstantExponentSet (n k : ℕ) : Set (Fin n →₀ ℕ) :=
  {e | 1 ≤ e.sum (fun _ n => n) ∧ e.sum (fun _ n => n) ≤ k}

def monomialIndexEquiv (n k : ℕ) : MonomialIndex n k ≃ nonconstantExponentSet n k where
  toFun α := ⟨monomialExponent α, by
    simpa [nonconstantExponentSet, sum_monomialExponent] using α.property⟩
  invFun e := ⟨fun i => ⟨e.val i, Nat.lt_succ_of_le ((exponent_le_sum e.val i).trans e.property.2)⟩,
    by
      have h : 1 ≤ e.val.sum (fun _ n => n) ∧ e.val.sum (fun _ n => n) ≤ k := e.property
      have hsum : e.val.sum (fun _ n => n) = ∑ i : Fin n, e.val i := by
        apply Finsupp.sum_fintype
        intro i
        rfl
      rw [hsum] at h
      exact h⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl

def zeroConstantPolynomialSpace (n k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.restrictSupport ℝ (nonconstantExponentSet n k)

theorem mem_zeroConstantPolynomialSpace (n k : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    P ∈ zeroConstantPolynomialSpace n k ↔ P.totalDegree ≤ k ∧ MvPolynomial.coeff 0 P = 0 := by
  classical
  change (↑P.support ⊆ nonconstantExponentSet n k) ↔ _
  constructor
  · intro h
    constructor
    · rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
      exact fun e he => (h he).2
    · by_contra hz
      have hh := (h (MvPolynomial.mem_support_iff.mpr hz)).1
      simp at hh
  · rintro ⟨hd, hz⟩ e he
    have hsum : e.sum (fun _ n => n) ≠ 0 := by
      intro hs
      have he0 : e = 0 := by
        ext i
        exact Nat.eq_zero_of_le_zero (hs ▸ exponent_le_sum e i)
      subst e
      exact (MvPolynomial.mem_support_iff.mp he) hz
    exact ⟨Nat.one_le_iff_ne_zero.mpr hsum, (MvPolynomial.le_totalDegree he).trans hd⟩

def nonconstantMonomialBasis (n k : ℕ) :
    Basis (MonomialIndex n k) ℝ (zeroConstantPolynomialSpace n k) :=
  (MvPolynomial.basisRestrictSupport ℝ (nonconstantExponentSet n k)).reindex
    (monomialIndexEquiv n k).symm

def coefficientPolynomialEquiv (n k : ℕ) :
    CoefficientSpace n k ≃ₗ[ℝ] zeroConstantPolynomialSpace n k :=
  (nonconstantMonomialBasis n k).equivFun.symm

def coefficientPolynomial {n k : ℕ} (F : CoefficientSpace n k) : MvPolynomial (Fin n) ℝ :=
  (coefficientPolynomialEquiv n k F).val

theorem nonconstantMonomialBasis_coe (n k : ℕ) (α : MonomialIndex n k) :
    ((nonconstantMonomialBasis n k) α).val =
      MvPolynomial.monomial (monomialExponent α) (1 : ℝ) := by
  classical
  have hb := congrArg (fun P : zeroConstantPolynomialSpace n k => P.val)
    (Basis.reindex_apply (MvPolynomial.basisRestrictSupport ℝ (nonconstantExponentSet n k))
      (monomialIndexEquiv n k).symm α)
  change ((nonconstantMonomialBasis n k) α).val = _ at hb
  rw [hb]
  change ((Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ) (nonconstantExponentSet n k)).symm
    (Finsupp.single ((monomialIndexEquiv n k) α) (1 : ℝ))).val =
      MvPolynomial.monomial (monomialExponent α) (1 : ℝ)
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single]
  rfl

theorem coefficientPolynomial_totalDegree {n k : ℕ} (F : CoefficientSpace n k) :
    (coefficientPolynomial F).totalDegree ≤ k :=
  ((mem_zeroConstantPolynomialSpace n k _).mp (coefficientPolynomialEquiv n k F).property).1

theorem coefficientPolynomial_constantCoeff {n k : ℕ} (F : CoefficientSpace n k) :
    MvPolynomial.coeff 0 (coefficientPolynomial F) = 0 :=
  ((mem_zeroConstantPolynomialSpace n k _).mp (coefficientPolynomialEquiv n k F).property).2

theorem coefficientPolynomial_eq_sum {n k : ℕ} (F : CoefficientSpace n k) :
    coefficientPolynomial F = ∑ α, MvPolynomial.monomial (monomialExponent α) (F α) := by
  change ((nonconstantMonomialBasis n k).equivFun.symm F).val = _
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, nonconstantMonomialBasis_coe,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem eval_coefficientPolynomial {n k : ℕ} (F : CoefficientSpace n k) (x : (PhysicalSpace n)) :
    MvPolynomial.eval x (coefficientPolynomial F) = phase F x := by
  rw [coefficientPolynomial_eq_sum, MvPolynomial.eval_sum]
  unfold phase
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · rfl
  · intro i
    simp

end PaperI.AllDim
