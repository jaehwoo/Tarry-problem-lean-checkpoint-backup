import PaperILean.OriginalUpperNormalPullback
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-! The actual quotient coefficient orbit in the six original affine coordinates.
Its polynomial format bound is uniform in the fixed seed coefficients. -/

noncomputable section
namespace PaperI.OriginalHaarOrbitPolynomial

open scoped BigOperators
open MvPolynomial

abbrev ParameterPolynomial := MvPolynomial (Fin 6) ℝ
abbrev SymbolicPolynomial := MvPolynomial (Fin 3) ParameterPolynomial

def ParameterDegreeBound (P : SymbolicPolynomial) (D : ℕ) : Prop :=
  ∀ e, (MvPolynomial.coeff e P).totalDegree ≤ D

theorem parameterDegree_mono {P : SymbolicPolynomial} {D E : ℕ}
    (hP : ParameterDegreeBound P D) (hDE : D ≤ E) : ParameterDegreeBound P E :=
  fun e => (hP e).trans hDE

theorem parameterDegree_C (p : ParameterPolynomial) (D : ℕ) (hp : p.totalDegree ≤ D) :
    ParameterDegreeBound (MvPolynomial.C p) D := by
  intro e
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hp
  · simp

theorem parameterDegree_X (i : Fin 3) (D : ℕ) :
    ParameterDegreeBound (MvPolynomial.X i) D := by
  intro e
  rw [MvPolynomial.coeff_X']
  split_ifs <;> simp

theorem parameterDegree_add {P Q : SymbolicPolynomial} {D : ℕ}
    (hP : ParameterDegreeBound P D) (hQ : ParameterDegreeBound Q D) :
    ParameterDegreeBound (P + Q) D := by
  intro e
  rw [MvPolynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP e) (hQ e))

theorem parameterDegree_mul {P Q : SymbolicPolynomial} {D E : ℕ}
    (hP : ParameterDegreeBound P D) (hQ : ParameterDegreeBound Q E) :
    ParameterDegreeBound (P * Q) (D + E) := by
  classical
  intro e
  rw [MvPolynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro z hz
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hP z.1) (hQ z.2))

theorem parameterDegree_pow {P : SymbolicPolynomial} {D : ℕ}
    (hP : ParameterDegreeBound P D) (n : ℕ) :
    ParameterDegreeBound (P ^ n) (n * D) := by
  induction n with
  | zero =>
      simpa using parameterDegree_C (1 : ParameterPolynomial) 0 (by simp)
  | succ n ih =>
      simpa [pow_succ, Nat.succ_mul] using parameterDegree_mul ih hP

theorem parameterDegree_sum {ι : Type*} (s : Finset ι) (P : ι → SymbolicPolynomial)
    (D : ℕ) (hP : ∀ i ∈ s, ParameterDegreeBound (P i) D) :
    ParameterDegreeBound (∑ i ∈ s, P i) D := by
  classical
  intro e
  rw [MvPolynomial.coeff_sum]
  exact MvPolynomial.totalDegree_finsetSum_le (fun i hi => hP i hi e)

theorem parameterDegree_prod {ι : Type*} (s : Finset ι) (P : ι → SymbolicPolynomial)
    (D : ι → ℕ) (hP : ∀ i ∈ s, ParameterDegreeBound (P i) (D i)) :
    ParameterDegreeBound (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using parameterDegree_C (1 : ParameterPolynomial) 0 (by simp)
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      exact parameterDegree_mul (hP a (by simp)) (ih (fun i hi => hP i (by simp [hi])))

/-- The three literal coordinates of the original upper-affine map. -/
def symbolicCoordinate : Fin 3 → SymbolicPolynomial :=
  ![MvPolynomial.X 0 + MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X 1 +
      MvPolynomial.C (MvPolynomial.X 1) * MvPolynomial.X 2 +
      MvPolynomial.C (MvPolynomial.X 2),
    MvPolynomial.X 1 + MvPolynomial.C (MvPolynomial.X 3) * MvPolynomial.X 2 +
      MvPolynomial.C (MvPolynomial.X 4),
    MvPolynomial.X 2 + MvPolynomial.C (MvPolynomial.X 5)]

theorem parameterDegree_symbolicCoordinate (i : Fin 3) :
    ParameterDegreeBound (symbolicCoordinate i) 1 := by
  have hC (j : Fin 6) : ParameterDegreeBound
      (MvPolynomial.C (MvPolynomial.X j : ParameterPolynomial)) 1 :=
    parameterDegree_C _ _ (by simp)
  have hCX (j : Fin 6) (l : Fin 3) : ParameterDegreeBound
      (MvPolynomial.C (MvPolynomial.X j : ParameterPolynomial) * MvPolynomial.X l) 1 := by
    simpa using parameterDegree_mul (hC j) (parameterDegree_X l 0)
  fin_cases i
  · exact parameterDegree_add
      (parameterDegree_add (parameterDegree_add (parameterDegree_X 0 1) (hCX 0 1))
        (hCX 1 2)) (hC 2)
  · exact parameterDegree_add (parameterDegree_add (parameterDegree_X 1 1) (hCX 3 2)) (hC 4)
  · exact parameterDegree_add (parameterDegree_X 2 1) (hC 5)

def symbolicOrbit {k : ℕ} (F : CoefficientSpace k) : SymbolicPolynomial :=
  ∑ α : MonomialIndex k,
    MvPolynomial.C (MvPolynomial.C (F α)) *
      ∏ i : Fin 3, symbolicCoordinate i ^ (α.val i).val

theorem parameterDegree_symbolicOrbit {k : ℕ} (F : CoefficientSpace k) :
    ParameterDegreeBound (symbolicOrbit F) k := by
  classical
  apply parameterDegree_sum
  intro α hα
  have hp : ParameterDegreeBound
      (∏ i : Fin 3, symbolicCoordinate i ^ (α.val i).val) (totalDegree α.val) := by
    simpa [PaperI.totalDegree] using
      parameterDegree_prod Finset.univ
        (fun i : Fin 3 => symbolicCoordinate i ^ (α.val i).val)
        (fun i : Fin 3 => (α.val i).val)
        (fun i hi => by simpa using
          parameterDegree_pow (parameterDegree_symbolicCoordinate i) (α.val i).val)
  have hterm : ParameterDegreeBound
      (MvPolynomial.C (MvPolynomial.C (F α)) *
        ∏ i : Fin 3, symbolicCoordinate i ^ (α.val i).val) (totalDegree α.val) := by
    simpa only [Nat.zero_add] using
      parameterDegree_mul (parameterDegree_C (MvPolynomial.C (F α)) 0 (by simp)) hp
  exact parameterDegree_mono hterm α.property.2

def orbitPolynomial {k : ℕ} (F : CoefficientSpace k) (α : MonomialIndex k) :
    ParameterPolynomial := MvPolynomial.coeff (monomialExponent α) (symbolicOrbit F)

theorem orbitPolynomial_degree {k : ℕ} (F : CoefficientSpace k) (α : MonomialIndex k) :
    (orbitPolynomial F α).totalDegree ≤ k :=
  parameterDegree_symbolicOrbit F (monomialExponent α)

theorem map_symbolicCoordinate (g : Fin 6 → ℝ) (i : Fin 3) :
    MvPolynomial.map (MvPolynomial.eval g) (symbolicCoordinate i) =
      affineCoordinate ![g 2,g 4,g 5] (originalUpperLinearMatrix g) i := by
  fin_cases i <;>
    simp [symbolicCoordinate, affineCoordinate, originalUpperLinearMatrix, Fin.sum_univ_succ] <;>
    ring

theorem map_symbolicOrbit {k : ℕ} (F : CoefficientSpace k) (g : Fin 6 → ℝ) :
    MvPolynomial.map (MvPolynomial.eval g) (symbolicOrbit F) =
      affinePolynomialMap ![g 2,g 4,g 5] (originalUpperLinearMatrix g) (coefficientPolynomial F) := by
  classical
  rw [coefficientPolynomial_eq_sum]
  simp only [symbolicOrbit, affinePolynomialMap, map_sum, map_mul, map_prod, map_pow,
    MvPolynomial.map_C, MvPolynomial.eval_C, map_symbolicCoordinate,
    MvPolynomial.aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  rw [Finsupp.prod_fintype]
  · rfl
  · intro i
    simp

theorem monomialExponent_injective {k : ℕ} :
    Function.Injective (monomialExponent : MonomialIndex k → Fin 3 →₀ ℕ) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun e : Fin 3 →₀ ℕ => e i) h

theorem coefficientPolynomial_coeff {k : ℕ} (F : CoefficientSpace k) (α : MonomialIndex k) :
    MvPolynomial.coeff (monomialExponent α) (coefficientPolynomial F) = F α := by
  classical
  simp [coefficientPolynomial_eq_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    monomialExponent_injective.eq_iff]

/-- Every retained quotient coefficient is a concrete polynomial in the actual group parameters. -/
theorem orbitPolynomial_eval {k : ℕ} (F : CoefficientSpace k)
    (g : Fin 6 → ℝ) (α : MonomialIndex k) :
    MvPolynomial.eval g (orbitPolynomial F α) = originalUpperCoefficientPullback F g α := by
  have hne : monomialExponent α ≠ 0 := by
    intro h
    have hpos := α.property.1
    rw [← sum_monomialExponent, h] at hpos
    simp at hpos
  have h := congrArg (MvPolynomial.coeff (monomialExponent α)) (map_symbolicOrbit F g)
  rw [MvPolynomial.coeff_map] at h
  change MvPolynomial.eval g (orbitPolynomial F α) = _ at h
  rw [← coefficientPolynomial_coeff (originalUpperCoefficientPullback F g) α,
    originalUpperCoefficientPullback, polynomial_affineCoefficientMap,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_C]
  simpa only [if_neg (Ne.symm hne), sub_zero] using h

end PaperI.OriginalHaarOrbitPolynomial
