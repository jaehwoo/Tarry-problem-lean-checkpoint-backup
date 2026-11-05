import PaperILean.AllDimCoefficientModel

/-! The actual degree-bounded polynomial quotient by the constant subspace. -/

open scoped BigOperators

noncomputable section
namespace PaperI.AllDim

variable {n : ℕ}

abbrev BoundedPolynomialSpace (n k : ℕ) := MvPolynomial.restrictTotalDegree (Fin n) ℝ k

def constantPolynomialSubspace (n k : ℕ) : Submodule ℝ (BoundedPolynomialSpace n k) where
  carrier := {P | ∃ c : ℝ, P.val = MvPolynomial.C c}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro P Q ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by simp [hc, hd]⟩
  smul_mem' := by
    rintro c P ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    change c • P.val = MvPolynomial.C (c * d)
    rw [hd, MvPolynomial.smul_eq_C_mul, map_mul]

def discardConstant (n k : ℕ) : BoundedPolynomialSpace n k →ₗ[ℝ] zeroConstantPolynomialSpace n k := by
  classical
  exact (Finsupp.restrictDom ℝ ℝ (nonconstantExponentSet n k)).comp
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ k).subtype

theorem nonzero_exponent_sum_pos (e : Fin n →₀ ℕ) (he : e ≠ 0) :
    1 ≤ e.sum (fun _ n => n) := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hs
  apply he
  ext i
  exact Nat.eq_zero_of_le_zero (hs ▸ exponent_le_sum e i)

theorem discardConstant_eq (n k : ℕ) (P : BoundedPolynomialSpace n k) :
    (discardConstant n k P).val = P.val - MvPolynomial.C (MvPolynomial.coeff 0 P.val) := by
  classical
  apply MvPolynomial.ext
  intro e
  change (Finsupp.filter (fun e => e ∈ nonconstantExponentSet n k) P.val) e = _
  rw [Finsupp.filter_apply, MvPolynomial.coeff_sub, MvPolynomial.coeff_C]
  by_cases he : e = 0
  · subst e
    simp [nonconstantExponentSet]
  · by_cases hk : e.sum (fun _ n => n) ≤ k
    · simp [nonconstantExponentSet, nonzero_exponent_sum_pos e he, hk, he, Ne.symm he]
      rfl
    · have hz : MvPolynomial.coeff e P.val = 0 := by
        apply MvPolynomial.not_mem_support_iff.mp
        intro hn
        have hd := (MvPolynomial.le_totalDegree hn).trans
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) k P.val).mp P.property)
        exact hk hd
      simp [nonconstantExponentSet, hk, he, Ne.symm he, hz]

theorem discardConstant_surjective (n k : ℕ) : Function.Surjective (discardConstant n k) := by
  intro Q
  have hQ := (mem_zeroConstantPolynomialSpace n k Q.val).mp Q.property
  refine ⟨⟨Q.val, (MvPolynomial.mem_restrictTotalDegree (Fin n) k Q.val).mpr hQ.1⟩, ?_⟩
  apply Subtype.ext
  rw [discardConstant_eq]
  simp [hQ.2]

theorem ker_discardConstant (n k : ℕ) :
    LinearMap.ker (discardConstant n k) = constantPolynomialSubspace n k := by
  ext P
  change discardConstant n k P = 0 ↔ ∃ c : ℝ, P.val = MvPolynomial.C c
  constructor
  · intro h
    have hv := congrArg (fun Q : zeroConstantPolynomialSpace n k => Q.val) h
    change (discardConstant n k P).val = 0 at hv
    rw [discardConstant_eq] at hv
    exact ⟨MvPolynomial.coeff 0 P.val, sub_eq_zero.mp hv⟩
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    rw [discardConstant_eq, hc]
    simp

def polynomialQuotientEquiv (n k : ℕ) :
    (BoundedPolynomialSpace n k ⧸ constantPolynomialSubspace n k) ≃ₗ[ℝ] CoefficientSpace n k :=
  (Submodule.quotEquivOfEq _ _ (ker_discardConstant n k).symm).trans
    (((discardConstant n k).quotKerEquivOfSurjective (discardConstant_surjective n k)).trans
      (coefficientPolynomialEquiv n k).symm)

end PaperI.AllDim
