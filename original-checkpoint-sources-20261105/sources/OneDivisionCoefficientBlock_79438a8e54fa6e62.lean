import PaperILean.QuadraticMonomialSpan
import PaperILean.WeightedGraphKernelABC
import Mathlib.LinearAlgebra.Matrix.Block

/-! Fixed manuscript I2156[122,597): the complete one-division coefficient-block
stage, including the actual C_k complement and actual lower-degree monomial basis.
The iterated filtration and subsequent factorial determinant assembly are separate. -/

noncomputable section
namespace PaperI.OneDivisionCoefficientBlock
open PaperI.QuadraticGridRestriction
open PaperI.QuadraticMonomialSpan
open MvPolynomial
open scoped BigOperators Matrix

/-- Ordinary total degree of a three-variable standard monomial. -/
def exponentDegree (e : Fin 3 → ℕ) : ℕ := e 0 + e 1 + e 2

def eligible (k : ℕ) (e : Fin 3 → ℕ) : Prop :=
  (e 0 = 0 ∧ e 1 + e 2 ≤ k) ∨ (1 ≤ e 0 ∧ exponentDegree e = k)

abbrev LowerIndex (k : ℕ) := {e : Fin 3 → ℕ // exponentDegree e + 2 ≤ k}
abbrev MissingIndex (k : ℕ) :=
  {e : Fin 3 → ℕ // 0 < e 0 ∧ exponentDegree e + 1 ≤ k}

def xShift (e : Fin 3 → ℕ) : Fin 3 → ℕ := ![e 0 + 1, e 1, e 2]
def xUnshift (e : Fin 3 → ℕ) : Fin 3 → ℕ := ![e 0 - 1, e 1, e 2]
def yShift (e : Fin 3 → ℕ) : Fin 3 → ℕ := ![e 0, e 1 + 2, e 2]
def yzShift (e : Fin 3 → ℕ) : Fin 3 → ℕ := ![e 0, e 1 + 1, e 2 + 1]
def zShift (e : Fin 3 → ℕ) : Fin 3 → ℕ := ![e 0, e 1, e 2 + 2]

theorem sourceExponent_sum (e : Fin 3 → ℕ) :
    (sourceExponent e).sum (fun _ n => n) = exponentDegree e := by
  simp [sourceExponent, Finsupp.sum_add_index', exponentDegree]

theorem sourceMonomial_coeff (e f : Fin 3 → ℕ) :
    coeff (sourceExponent e) (sourceMonomial f) = if f = e then 1 else 0 := by
  classical
  rw [sourceMonomial_eq_monomial, coeff_monomial]
  simp only [sourceExponent_injective.eq_iff]

/-- This is membership in the actual saved C_k submodule, not merely its index set. -/
theorem sourceMonomial_mem_span_iff (k : ℕ) (e : Fin 3 → ℕ) :
    sourceMonomial e ∈ monomialSpan k ↔ eligible k e := by
  classical
  constructor
  · intro hm
    by_contra hne
    have hz : ∀ p ∈ monomialSpan k, coeff (sourceExponent e) p = 0 := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
          rcases hp with ⟨f, rfl⟩
          rw [sourceMonomial_coeff, if_neg]
          intro hfe
          apply hne
          subst e
          exact f.property
      | zero => simp
      | add p q hp hq hp' hq' => simp [coeff_add, hp', hq']
      | smul a p hp hp' => simp [coeff_smul, hp']
    have hc := hz (sourceMonomial e) hm
    simp only [sourceMonomial_coeff, if_pos rfl] at hc
    exact one_ne_zero hc
  · intro he
    exact Submodule.subset_span ⟨⟨e, he⟩, rfl⟩

/-- Exact missing rows in the ordinary degree-at-most-k ambient monomial family. -/
theorem missing_rows_iff (k : ℕ) (e : Fin 3 → ℕ) (he : exponentDegree e ≤ k) :
    sourceMonomial e ∉ monomialSpan k ↔
      0 < e 0 ∧ exponentDegree e + 1 ≤ k := by
  rw [sourceMonomial_mem_span_iff]
  unfold eligible exponentDegree at *
  omega

def shiftEquiv (k : ℕ) : LowerIndex k ≃ MissingIndex k where
  toFun e := ⟨xShift e.val, by
    have he := e.property
    simp only [xShift, exponentDegree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
    omega⟩
  invFun e := ⟨xUnshift e.val, by
    have he := e.property
    simp only [xUnshift, exponentDegree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
    omega⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [xShift, xUnshift]
  right_inv e := by
    apply Subtype.ext
    have he := e.property.1
    funext i
    fin_cases i <;> simp [xShift, xUnshift]
    omega

theorem x_mul_sourceMonomial (e : Fin 3 → ℕ) :
    X 0 * sourceMonomial e = sourceMonomial (xShift e) := by
  simp only [sourceMonomial, xShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_add, pow_one]
  ring

theorem lower_monomials_linearIndependent (k : ℕ) :
    LinearIndependent ℝ (fun e : LowerIndex k => sourceMonomial e.val) := by
  have hi : Function.Injective (fun e : LowerIndex k => sourceExponent e.val) := by
    intro e f h
    exact Subtype.ext (sourceExponent_injective h)
  simpa only [MvPolynomial.coe_basisMonomials, sourceMonomial_eq_monomial] using
    (MvPolynomial.basisMonomials (Fin 3) ℝ).linearIndependent.comp
      (fun e : LowerIndex k => sourceExponent e.val) hi

/-- The monomial family spans the actual saved lower-degree space, including k<2. -/
theorem lower_monomials_span (k : ℕ) :
    Submodule.span ℝ (Set.range (fun e : LowerIndex k => sourceMonomial e.val)) =
      GraphRestrictionKernel.lowerDegreeSpace k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨e, rfl⟩
    have hk : 2 ≤ k := by have := e.property; omega
    simp only [GraphRestrictionKernel.lowerDegreeSpace, if_pos hk]
    apply (mem_restrictTotalDegree _ _ _).mpr
    rw [sourceMonomial_eq_monomial, totalDegree_monomial _ one_ne_zero,
      sourceExponent_sum]
    have := e.property
    omega
  · intro p hp
    by_cases hk : 2 ≤ k
    · have hd : p.totalDegree ≤ k - 2 := by
        apply (mem_restrictTotalDegree _ _ _).mp
        simpa only [GraphRestrictionKernel.lowerDegreeSpace, if_pos hk] using hp
      rw [p.as_sum]
      apply Submodule.sum_mem
      intro n hn
      have hn' : n.sum (fun _ e => e) ≤ k - 2 := (le_totalDegree hn).trans hd
      let e : Fin 3 → ℕ := fun i => n i
      have hen : sourceExponent e = n := by ext i; simp [e]
      have he : exponentDegree e + 2 ≤ k := by
        rw [← hen, sourceExponent_sum] at hn'
        omega
      have hm : sourceMonomial e ∈ Submodule.span ℝ
          (Set.range (fun e : LowerIndex k => sourceMonomial e.val)) :=
        Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
      have heq : monomial n (coeff n p) = coeff n p • sourceMonomial e := by
        rw [sourceMonomial_eq_monomial, hen, smul_monomial, smul_eq_mul, mul_one]
      rw [heq]
      exact Submodule.smul_mem _ _ hm
    · have hp0 : p = 0 := by
        simpa only [GraphRestrictionKernel.lowerDegreeSpace, if_neg hk,
          Submodule.mem_bot] using hp
      rw [hp0]
      exact Submodule.zero_mem _

instance lowerIndexFinite (k : ℕ) : Finite (LowerIndex k) := by
  let code : LowerIndex k → (Fin 3 → Fin (k + 1)) := fun e i =>
    ⟨e.val i, by
      have he := e.property
      fin_cases i <;> simp only [exponentDegree] at he <;> dsimp <;> omega⟩
  apply Finite.of_injective code
  intro e f h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance lowerIndexFintype (k : ℕ) : Fintype (LowerIndex k) :=
  Fintype.ofFinite _

def quadratic (A B C : ℝ) : TriPoly :=
  MvPolynomial.C A * X 1 ^ 2 + MvPolynomial.C B * X 1 * X 2 +
    MvPolynomial.C C * X 2 ^ 2

theorem graphEquation_eq (A B C : ℝ) :
    WeightedGraphKernelABC.graphEquation A B C = X 0 - quadratic A B C := rfl

/-- Literal Q-times-monomial expansion; coefficients may vanish or have any sign. -/
theorem quadratic_mul_sourceMonomial (A B C : ℝ) (e : Fin 3 → ℕ) :
    quadratic A B C * sourceMonomial e =
      MvPolynomial.C A * sourceMonomial (yShift e) +
      MvPolynomial.C B * sourceMonomial (yzShift e) +
      MvPolynomial.C C * sourceMonomial (zShift e) := by
  simp only [quadratic, sourceMonomial, yShift, yzShift, zShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_add, pow_one]
  ring

theorem quadratic_coeff (A B C : ℝ) (e v : Fin 3 → ℕ) :
    coeff (sourceExponent v) (quadratic A B C * sourceMonomial e) =
      (if yShift e = v then A else 0) + (if yzShift e = v then B else 0) +
      (if zShift e = v then C else 0) := by
  classical
  rw [quadratic_mul_sourceMonomial]
  simp only [coeff_add, coeff_C_mul, sourceMonomial_coeff]
  split_ifs <;> simp_all

/-- Every actual nonzero Q coefficient has unchanged x exponent and two added degrees. -/
theorem quadratic_support_degree (A B C : ℝ) (e v : Fin 3 → ℕ)
    (h : coeff (sourceExponent v) (quadratic A B C * sourceMonomial e) ≠ 0) :
    v 0 = e 0 ∧ exponentDegree v = exponentDegree e + 2 := by
  classical
  rw [quadratic_coeff] at h
  by_cases hy : yShift e = v
  · subst v
    simp [yShift, exponentDegree]
    omega
  by_cases hyz : yzShift e = v
  · subst v
    simp [yzShift, exponentDegree]
    omega
  by_cases hz : zShift e = v
  · subst v
    simp [zShift, exponentDegree]
    omega
  simp [hy, hyz, hz] at h

/-- Binary terms discarded from the remaining block lie in the actual saved C_k. -/
theorem binary_quadratic_term_mem_span (k : ℕ) (A B C : ℝ) (e : LowerIndex k)
    (v : Fin 3 → ℕ) (hv : v 0 = 0)
    (hc : coeff (sourceExponent v) (quadratic A B C * sourceMonomial e.val) ≠ 0) :
    sourceMonomial v ∈ monomialSpan k := by
  apply (sourceMonomial_mem_span_iff k v).mpr
  left
  refine ⟨hv, ?_⟩
  have hd := (quadratic_support_degree A B C e.val v hc).2
  have he := e.property
  unfold exponentDegree at *
  omega

/-- The literal coefficient matrix remaining after the actual C_k rows are removed. -/
def remainingMatrix (k : ℕ) (A B C : ℝ) : Matrix (LowerIndex k) (LowerIndex k) ℝ :=
  fun e f => coeff (sourceExponent (xShift e.val))
    (WeightedGraphKernelABC.graphEquation A B C * sourceMonomial f.val)

def gradeIndex (k : ℕ) (e : LowerIndex k) : Fin (k + 1) :=
  ⟨exponentDegree e.val, by have := e.property; omega⟩

theorem remainingMatrix_at_or_below_grade (k : ℕ) (A B C : ℝ)
    (e f : LowerIndex k) (h : exponentDegree e.val ≤ exponentDegree f.val) :
    remainingMatrix k A B C e f = if f = e then 1 else 0 := by
  classical
  unfold remainingMatrix
  rw [graphEquation_eq, sub_mul, coeff_sub, x_mul_sourceMonomial, sourceMonomial_coeff]
  have hq : coeff (sourceExponent (xShift e.val))
      (quadratic A B C * sourceMonomial f.val) = 0 := by
    by_contra hq
    have hd := (quadratic_support_degree A B C f.val (xShift e.val) hq).2
    simp only [xShift, exponentDegree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hd h
    omega
  rw [hq, sub_zero]
  have hinj : Function.Injective xShift := by
    intro v w h
    funext i
    fin_cases i
    · have hh := congrFun h 0
      simp only [xShift, Matrix.cons_val_zero] at hh
      omega
    · exact congrFun h 1
    · exact congrFun h 2
  simp only [hinj.eq_iff, Subtype.val_inj]

theorem remainingMatrix_zero_of_grade_lt (k : ℕ) (A B C : ℝ)
    (e f : LowerIndex k) (h : exponentDegree e.val < exponentDegree f.val) :
    remainingMatrix k A B C e f = 0 := by
  rw [remainingMatrix_at_or_below_grade k A B C e f (Nat.le_of_lt h), if_neg]
  intro hfe
  subst f
  omega

theorem remainingMatrix_blockTriangular (k : ℕ) (A B C : ℝ) :
    (remainingMatrix k A B C)ᵀ.BlockTriangular (gradeIndex k) := by
  intro e f h
  change remainingMatrix k A B C f e = 0
  exact remainingMatrix_zero_of_grade_lt k A B C f e h

theorem remainingMatrix_diagonal_blocks (k : ℕ) (A B C : ℝ) (a : Fin (k + 1)) :
    (remainingMatrix k A B C)ᵀ.toSquareBlock (gradeIndex k) a = 1 := by
  classical
  ext e f
  change remainingMatrix k A B C f.val e.val = if e = f then 1 else 0
  have hg : exponentDegree f.val.val = exponentDegree e.val.val :=
    congrArg Fin.val (f.property.trans e.property.symm)
  simpa only [Subtype.val_inj, eq_comm] using
    remainingMatrix_at_or_below_grade k A B C f.val e.val (Nat.le_of_eq hg)

theorem remainingMatrix_det (k : ℕ) (A B C : ℝ) :
    (remainingMatrix k A B C).det = 1 := by
  classical
  calc
    (remainingMatrix k A B C).det = (remainingMatrix k A B C)ᵀ.det :=
      (Matrix.det_transpose _).symm
    _ = ∏ a : Fin (k + 1),
        ((remainingMatrix k A B C)ᵀ.toSquareBlock (gradeIndex k) a).det :=
      (remainingMatrix_blockTriangular k A B C).det_fintype
    _ = 1 := by simp_rw [remainingMatrix_diagonal_blocks, Matrix.det_one]; simp

/-- Complete one-division coefficient-block proof stage at fixed I2156[122,597).
There is no theorem-shaped premise: all real A,B,C are allowed, hence both charts. -/
theorem one_division_coefficient_stage (k : ℕ) (A B C : ℝ) :
    (∀ e : Fin 3 → ℕ, exponentDegree e ≤ k →
      (sourceMonomial e ∉ monomialSpan k ↔
        0 < e 0 ∧ exponentDegree e + 1 ≤ k)) ∧
    LinearIndependent ℝ (fun e : LowerIndex k => sourceMonomial e.val) ∧
    Submodule.span ℝ (Set.range (fun e : LowerIndex k => sourceMonomial e.val)) =
      GraphRestrictionKernel.lowerDegreeSpace k ∧
    Function.Bijective (shiftEquiv k) ∧
    (∀ e : LowerIndex k,
      X 0 * sourceMonomial e.val = sourceMonomial ((shiftEquiv k e).val)) ∧
    (∀ (e : LowerIndex k) (v : Fin 3 → ℕ),
      coeff (sourceExponent v) (quadratic A B C * sourceMonomial e.val) ≠ 0 →
      v 0 = e.val 0 ∧ exponentDegree v = exponentDegree (xShift e.val) + 1) ∧
    (∀ (e : LowerIndex k) (v : Fin 3 → ℕ), v 0 = 0 →
      coeff (sourceExponent v) (quadratic A B C * sourceMonomial e.val) ≠ 0 →
      sourceMonomial v ∈ monomialSpan k) ∧
    (remainingMatrix k A B C)ᵀ.BlockTriangular (gradeIndex k) ∧
    (∀ a : Fin (k + 1),
      (remainingMatrix k A B C)ᵀ.toSquareBlock (gradeIndex k) a = 1) ∧
    (remainingMatrix k A B C).det = 1 := by
  refine ⟨missing_rows_iff k, lower_monomials_linearIndependent k,
    lower_monomials_span k, (shiftEquiv k).bijective, ?_, ?_,
    binary_quadratic_term_mem_span k A B C,
    remainingMatrix_blockTriangular k A B C,
    remainingMatrix_diagonal_blocks k A B C, remainingMatrix_det k A B C⟩
  · intro e
    exact x_mul_sourceMonomial e.val
  · intro e v hc
    obtain ⟨hx, hd⟩ := quadratic_support_degree A B C e.val v hc
    refine ⟨hx, ?_⟩
    simp only [xShift, exponentDegree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hd ⊢
    omega

end PaperI.OneDivisionCoefficientBlock
