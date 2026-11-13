import PaperILean.MainStatement
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Linarith

/-! Complete nonconstant monomial coefficients, with no degree restriction
beyond the manuscript's total-degree condition. -/

open scoped BigOperators

noncomputable section
namespace PaperI

def monomialExponent {k : ℕ} (α : MonomialIndex k) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.val i).val)

@[simp] theorem monomialExponent_apply {k : ℕ} (α : MonomialIndex k) (i : Fin 3) :
    monomialExponent α i = (α.val i).val := rfl

theorem sum_monomialExponent {k : ℕ} (α : MonomialIndex k) :
    (monomialExponent α).sum (fun _ e => e) = totalDegree α.val := by
  rw [Finsupp.sum_fintype]
  · rfl
  · intro i
    rfl

theorem exponent_le_sum (e : Fin 3 →₀ ℕ) (i : Fin 3) :
    e i ≤ e.sum (fun _ n => n) := by
  rw [Finsupp.sum_fintype]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · intro i
    rfl

def nonconstantExponentSet (k : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | 1 ≤ e.sum (fun _ n => n) ∧ e.sum (fun _ n => n) ≤ k}

def monomialIndexEquiv (k : ℕ) : MonomialIndex k ≃ nonconstantExponentSet k where
  toFun α := ⟨monomialExponent α, by
    simpa [nonconstantExponentSet, sum_monomialExponent] using α.property⟩
  invFun e := ⟨fun i => ⟨e.val i, Nat.lt_succ_of_le ((exponent_le_sum e.val i).trans e.property.2)⟩,
    by
      have h : 1 ≤ e.val.sum (fun _ n => n) ∧ e.val.sum (fun _ n => n) ≤ k := e.property
      have hsum : e.val.sum (fun _ n => n) = ∑ i : Fin 3, e.val i := by
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

def zeroConstantPolynomialSpace (k : ℕ) : Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  MvPolynomial.restrictSupport ℝ (nonconstantExponentSet k)

theorem mem_zeroConstantPolynomialSpace (k : ℕ) (P : MvPolynomial (Fin 3) ℝ) :
    P ∈ zeroConstantPolynomialSpace k ↔ P.totalDegree ≤ k ∧ MvPolynomial.coeff 0 P = 0 := by
  classical
  change (↑P.support ⊆ nonconstantExponentSet k) ↔ _
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

def nonconstantMonomialBasis (k : ℕ) :
    Basis (MonomialIndex k) ℝ (zeroConstantPolynomialSpace k) :=
  (MvPolynomial.basisRestrictSupport ℝ (nonconstantExponentSet k)).reindex
    (monomialIndexEquiv k).symm

def coefficientPolynomialEquiv (k : ℕ) :
    CoefficientSpace k ≃ₗ[ℝ] zeroConstantPolynomialSpace k :=
  (nonconstantMonomialBasis k).equivFun.symm

def coefficientPolynomial {k : ℕ} (F : CoefficientSpace k) : MvPolynomial (Fin 3) ℝ :=
  (coefficientPolynomialEquiv k F).val

theorem nonconstantMonomialBasis_coe (k : ℕ) (α : MonomialIndex k) :
    ((nonconstantMonomialBasis k) α).val =
      MvPolynomial.monomial (monomialExponent α) (1 : ℝ) := by
  classical
  have hb := congrArg (fun P : zeroConstantPolynomialSpace k => P.val)
    (Basis.reindex_apply (MvPolynomial.basisRestrictSupport ℝ (nonconstantExponentSet k))
      (monomialIndexEquiv k).symm α)
  change ((nonconstantMonomialBasis k) α).val = _ at hb
  rw [hb]
  change ((Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ) (nonconstantExponentSet k)).symm
    (Finsupp.single ((monomialIndexEquiv k) α) (1 : ℝ))).val =
      MvPolynomial.monomial (monomialExponent α) (1 : ℝ)
  rw [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_single]
  rfl

theorem coefficientPolynomial_totalDegree {k : ℕ} (F : CoefficientSpace k) :
    (coefficientPolynomial F).totalDegree ≤ k :=
  ((mem_zeroConstantPolynomialSpace k _).mp (coefficientPolynomialEquiv k F).property).1

theorem coefficientPolynomial_constantCoeff {k : ℕ} (F : CoefficientSpace k) :
    MvPolynomial.coeff 0 (coefficientPolynomial F) = 0 :=
  ((mem_zeroConstantPolynomialSpace k _).mp (coefficientPolynomialEquiv k F).property).2

theorem coefficientPolynomial_eq_sum {k : ℕ} (F : CoefficientSpace k) :
    coefficientPolynomial F = ∑ α, MvPolynomial.monomial (monomialExponent α) (F α) := by
  change ((nonconstantMonomialBasis k).equivFun.symm F).val = _
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, nonconstantMonomialBasis_coe,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem eval_coefficientPolynomial {k : ℕ} (F : CoefficientSpace k) (x : PhysicalSpace) :
    MvPolynomial.eval x (coefficientPolynomial F) = phase F x := by
  rw [coefficientPolynomial_eq_sum, MvPolynomial.eval_sum]
  unfold phase
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · rfl
  · intro i
    simp

end PaperI
