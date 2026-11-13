import PaperILean.CoefficientModel

/-! The actual degree-bounded polynomial quotient by the constant subspace. -/

open scoped BigOperators

noncomputable section
namespace PaperI

abbrev BoundedPolynomialSpace (k : ℕ) := MvPolynomial.restrictTotalDegree (Fin 3) ℝ k

def constantPolynomialSubspace (k : ℕ) : Submodule ℝ (BoundedPolynomialSpace k) where
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

def discardConstant (k : ℕ) : BoundedPolynomialSpace k →ₗ[ℝ] zeroConstantPolynomialSpace k := by
  classical
  exact (Finsupp.restrictDom ℝ ℝ (nonconstantExponentSet k)).comp
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ k).subtype

theorem nonzero_exponent_sum_pos (e : Fin 3 →₀ ℕ) (he : e ≠ 0) :
    1 ≤ e.sum (fun _ n => n) := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hs
  apply he
  ext i
  exact Nat.eq_zero_of_le_zero (hs ▸ exponent_le_sum e i)

theorem discardConstant_eq (k : ℕ) (P : BoundedPolynomialSpace k) :
    (discardConstant k P).val = P.val - MvPolynomial.C (MvPolynomial.coeff 0 P.val) := by
  classical
  apply MvPolynomial.ext
  intro e
  change (Finsupp.filter (fun e => e ∈ nonconstantExponentSet k) P.val) e = _
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
          ((MvPolynomial.mem_restrictTotalDegree (Fin 3) k P.val).mp P.property)
        exact hk hd
      simp [nonconstantExponentSet, hk, he, Ne.symm he, hz]

theorem discardConstant_surjective (k : ℕ) : Function.Surjective (discardConstant k) := by
  intro Q
  have hQ := (mem_zeroConstantPolynomialSpace k Q.val).mp Q.property
  refine ⟨⟨Q.val, (MvPolynomial.mem_restrictTotalDegree (Fin 3) k Q.val).mpr hQ.1⟩, ?_⟩
  apply Subtype.ext
  rw [discardConstant_eq]
  simp [hQ.2]

theorem ker_discardConstant (k : ℕ) :
    LinearMap.ker (discardConstant k) = constantPolynomialSubspace k := by
  ext P
  change discardConstant k P = 0 ↔ ∃ c : ℝ, P.val = MvPolynomial.C c
  constructor
  · intro h
    have hv := congrArg (fun Q : zeroConstantPolynomialSpace k => Q.val) h
    change (discardConstant k P).val = 0 at hv
    rw [discardConstant_eq] at hv
    exact ⟨MvPolynomial.coeff 0 P.val, sub_eq_zero.mp hv⟩
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    rw [discardConstant_eq, hc]
    simp

def polynomialQuotientEquiv (k : ℕ) :
    (BoundedPolynomialSpace k ⧸ constantPolynomialSubspace k) ≃ₗ[ℝ] CoefficientSpace k :=
  (Submodule.quotEquivOfEq _ _ (ker_discardConstant k).symm).trans
    (((discardConstant k).quotKerEquivOfSurjective (discardConstant_surjective k)).trans
      (coefficientPolynomialEquiv k).symm)

end PaperI
