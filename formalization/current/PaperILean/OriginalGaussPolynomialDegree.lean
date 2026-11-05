import PaperILean.OriginalNormalPolynomial

/-! I1283: the exact two polynomials at fixed real p,z have degree at most
D=k-m+1 and D-1. Specialization, cancellation, zero polynomials and lower
actual degrees are retained. This module alone asserts no root count.
-/
noncomputable section
namespace PaperI
open scoped BigOperators

def originalGaussPolynomialSlice (Q : MvPolynomial (Fin 3) ℝ) (z : ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.C z] Q

theorem originalGaussPolynomialSlice_eval (Q : MvPolynomial (Fin 3) ℝ) (z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval w (originalGaussPolynomialSlice Q z)=MvPolynomial.eval ![w 0,w 1,z] Q := by
  change MvPolynomial.eval w (MvPolynomial.eval₂ MvPolynomial.C
    ![MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.C z] Q)=_
  rw [← MvPolynomial.eval_assoc]
  have he : MvPolynomial.eval w ∘
      (![MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.C z] : Fin 3 → MvPolynomial (Fin 2) ℝ)=
      ![w 0,w 1,z] := by
    ext i
    fin_cases i <;> simp
  rw [he]

theorem originalGaussPolynomialSlice_totalDegree (Q : MvPolynomial (Fin 3) ℝ) (z : ℝ) :
    (originalGaussPolynomialSlice Q z).totalDegree≤Q.totalDegree := by
  classical
  let v : Fin 3 → MvPolynomial (Fin 2) ℝ := ![MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.C z]
  have hv : ∀ i, (v i).totalDegree≤1 := by
    intro i
    fin_cases i <;> simp [v]
  change (MvPolynomial.eval₂ MvPolynomial.C v Q).totalDegree≤Q.totalDegree
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  calc
    (MvPolynomial.C (Q.coeff d)*∏ i ∈ d.support, v i^d i).totalDegree
        ≤(MvPolynomial.C (Q.coeff d)).totalDegree+(∏ i ∈ d.support, v i^d i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _=(∏ i ∈ d.support, v i^d i).totalDegree := by simp
    _≤∑ i ∈ d.support, (v i^d i).totalDegree := MvPolynomial.totalDegree_finset_prod _ _
    _≤∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
      (MvPolynomial.totalDegree_pow (v i) (d i)).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _≤Q.totalDegree := MvPolynomial.le_totalDegree hd

theorem originalGauss_polynomial_pair_eval {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (p z : ℝ) (w : Fin 2 → ℝ) :
    MvPolynomial.eval w (originalGaussPolynomialSlice (originalNormalPolynomial F n) z)=
        originalNormalPhase F n ![w 0,w 1,z] ∧
    MvPolynomial.eval w (originalGaussPolynomialSlice (originalGaussSecondPolynomial F n p) z)=
        fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,z] ![0,1,0]+
          p*fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,z] ![1,0,0] := by
  constructor
  · rw [originalGaussPolynomialSlice_eval,originalNormalPhase_eq_eval]
  · rw [originalGaussPolynomialSlice_eval,originalGaussSecondPolynomial_eval]

theorem originalGauss_manuscript_slice_degrees {k : ℕ} (F : CoefficientSpace k) (m : ℕ)
    (hm : 2≤m) (hmk : m≤k/2) (p z : ℝ) :
    (originalGaussPolynomialSlice (originalNormalPolynomial F (m-1)) z).totalDegree≤k-m+1 ∧
    (originalGaussPolynomialSlice (originalGaussSecondPolynomial F (m-1) p) z).totalDegree≤(k-m+1)-1 := by
  have hmk' : m≤k := hmk.trans (Nat.div_le_self k 2)
  have he : k-(m-1)=k-m+1 := by omega
  constructor
  · exact (originalGaussPolynomialSlice_totalDegree _ z).trans
      (by simpa only [he] using originalNormalPolynomial_totalDegree F (m-1))
  · exact (originalGaussPolynomialSlice_totalDegree _ z).trans
      (by simpa only [he] using originalGaussSecondPolynomial_totalDegree F (m-1) p)

end PaperI
