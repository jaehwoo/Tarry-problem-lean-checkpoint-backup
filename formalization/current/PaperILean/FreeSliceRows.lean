import PaperILean.PhysicalGaussPivot
import PaperILean.CoefficientJetBounds
import PaperILean.PolynomialDerivativeCoefficients

/-! Actual ordinary Gauss normalization rows and the degree guard for
I3353[269,409). The degree bound is derived from the same selected graph.
No coordinate or determinant premise is substituted for a source hypothesis. -/

noncomputable section
namespace PaperI.FreeSliceRows

open Filter
open scoped Topology BigOperators

/-- Exponents of x, xy, xz, xyz in the order of the four ordinary raw rows. -/
def normalRowExponent (i : Fin 4) : Fin 3 →₀ ℕ :=
  ![Finsupp.single 0 1,
    Finsupp.single 1 1 + Finsupp.single 0 1,
    Finsupp.single 2 1 + Finsupp.single 0 1,
    Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 0 1] i

/-- The actual raw equations at the normalized endpoint, before row extraction. -/
def rawRows (P : MvPolynomial (Fin 3) ℝ) : Fin 4 → ℝ :=
  ![MvPolynomial.eval 0 (MvPolynomial.pderiv 0 P),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 P)),
    MvPolynomial.eval 0 (MvPolynomial.pderiv 1
      (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 P)))]

theorem rawRows_eq_coeff (P : MvPolynomial (Fin 3) ℝ) (i : Fin 4) :
    rawRows P i = MvPolynomial.coeff (normalRowExponent i) P := by
  fin_cases i <;>
    simp only [rawRows, normalRowExponent, Matrix.cons_val_zero, Matrix.cons_val_succ,
      MvPolynomial.eval_zero] <;>
    change MvPolynomial.coeff 0 _ = _ <;>
    rw [constantCoeff_polynomialPartial] <;>
    simp [coeff_polynomialPartial, Finsupp.single_apply]

theorem normalRowExponent_injective : Function.Injective normalRowExponent := by
  intro i j h
  have h1 := congrArg (fun e : Fin 3 →₀ ℕ => e 1) h
  have h2 := congrArg (fun e : Fin 3 →₀ ℕ => e 2) h
  fin_cases i <;> fin_cases j <;>
    norm_num [normalRowExponent, Finsupp.single_apply, Fin.ext_iff] at h1 h2 ⊢

theorem normalRowExponent_degree (i : Fin 4) :
    1 ≤ (normalRowExponent i).sum (fun _ n => n) ∧
      (normalRowExponent i).sum (fun _ n => n) ≤ 3 := by
  have hsum : (normalRowExponent i).sum (fun _ n => n) =
      ∑ j : Fin 3, normalRowExponent i j :=
    Finsupp.sum_fintype _ _ (by intro j; rfl)
  rw [hsum]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i <;> norm_num [normalRowExponent, Fin.sum_univ_succ,
    Finsupp.single_apply, h01, h02, h10, h12, h20, h21]

/-- The four genuine coefficient indices, after the degree guard is established. -/
def normalIndex {k : ℕ} (hk : 3 ≤ k) (i : Fin 4) : MonomialIndex k :=
  (monomialIndexEquiv k).symm ⟨normalRowExponent i,
    (normalRowExponent_degree i).1, (normalRowExponent_degree i).2.trans hk⟩

theorem monomialExponent_normalIndex {k : ℕ} (hk : 3 ≤ k) (i : Fin 4) :
    monomialExponent (normalIndex hk i) = normalRowExponent i := by
  exact congrArg Subtype.val ((monomialIndexEquiv k).apply_symm_apply
    ⟨normalRowExponent i,
      (normalRowExponent_degree i).1, (normalRowExponent_degree i).2.trans hk⟩)

theorem normalIndex_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (normalIndex hk) := by
  intro i j h
  apply normalRowExponent_injective
  simpa only [monomialExponent_normalIndex] using congrArg monomialExponent h

theorem rawRows_coefficient {k : ℕ} (J : CoefficientSpace k) (hk : 3 ≤ k)
    (i : Fin 4) : rawRows (coefficientPolynomial J) i = J (normalIndex hk i) := by
  rw [rawRows_eq_coeff, ← monomialExponent_normalIndex hk i, coefficientPolynomial_coeff]

/-- The degree-three test row retains its raw factorial two. -/
theorem raw_xyy_eq_twice_coeff (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.eval 0
        (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P))) =
      2 * MvPolynomial.coeff (Finsupp.single 1 2 + Finsupp.single 0 1) P := by
  rw [MvPolynomial.eval_zero]
  change MvPolynomial.coeff 0 _ = _
  rw [constantCoeff_polynomialPartial, coeff_polynomialPartial, coeff_polynomialPartial]
  have he : (Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 0 1 :
      Fin 3 →₀ ℕ) = Finsupp.single 1 2 + Finsupp.single 0 1 := by
    ext i
    fin_cases i <;> simp
  norm_num [Finsupp.single_apply, he]

/-- Regularity of the same normalized root graph excludes degrees below three.
Neither a degree assumption nor the desired polynomial derivative is a premise. -/
theorem degree_ge_three_of_regular_graph {k : ℕ} (J : CoefficientSpace k)
    (c : (Fin 2 → ℝ) → ℝ)
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) (hDc : fderiv ℝ c 0 = 0)
    (hroot : ∀ᶠ v in 𝓝 0,
      MvPolynomial.eval ![c v, v 0, v 1]
        (MvPolynomial.pderiv 0 (coefficientPolynomial J)) = 0)
    (hlam : MvPolynomial.eval 0
      (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (coefficientPolynomial J))) ≠ 0)
    (hr : PhysicalGaussPivot.graphYY c ≠ 0) : 3 ≤ k := by
  have hyy := PhysicalGaussPivot.graph_yy_derivative
    (MvPolynomial.pderiv 0 (coefficientPolynomial J)) c hc hc0 hDc hroot hlam
  have hne : MvPolynomial.eval 0
      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 0 (coefficientPolynomial J)))) ≠ 0 := by
    rw [hyy]
    exact mul_ne_zero (neg_ne_zero.mpr hlam) hr
  rw [raw_xyy_eq_twice_coeff] at hne
  have hcoeff : MvPolynomial.coeff (Finsupp.single 1 2 + Finsupp.single 0 1)
      (coefficientPolynomial J) ≠ 0 := (mul_ne_zero_iff.mp hne).2
  have hdeg := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)).trans
    (coefficientPolynomial_totalDegree J)
  have hsum : (Finsupp.single 1 2 + Finsupp.single 0 1 : Fin 3 →₀ ℕ).sum
      (fun _ n => n) = 3 := by
    rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    norm_num [Fin.sum_univ_succ, Finsupp.single_apply, h02, h12]
  simpa only [hsum] using hdeg

end PaperI.FreeSliceRows
