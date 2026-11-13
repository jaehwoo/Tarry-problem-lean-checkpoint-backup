import PaperILean.PolynomialSignDescription
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Substitute actual base coordinates into a polynomial family. Evaluation
is exact and total degree cannot increase, including cancellation and degree
drops. Pre-strategy specialization obstructions were executed in record041. -/

noncomputable section
namespace PaperI
open MvPolynomial
open scoped BigOperators

def specializePolynomialFiber {ι κ : Type*} (p : ι → ℝ)
    (q : MvPolynomial (ι ⊕ κ) ℝ) : MvPolynomial κ ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.C (p i)) MvPolynomial.X) q

theorem specializePolynomialFiber_eval {ι κ : Type*} (p : ι → ℝ)
    (q : MvPolynomial (ι ⊕ κ) ℝ) (x : κ → ℝ) :
    MvPolynomial.eval x (specializePolynomialFiber p q) =
      MvPolynomial.eval (Sum.elim p x) q := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.C (p i)) MvPolynomial.X) q) = _
  rw [← MvPolynomial.eval_assoc]
  have h : (MvPolynomial.eval x ∘
      Sum.elim (fun i => MvPolynomial.C (p i)) MvPolynomial.X) = Sum.elim p x := by
    funext j
    cases j <;> simp
  rw [h]

theorem specializePolynomialFiber_totalDegree_le {ι κ : Type*} (p : ι → ℝ)
    (q : MvPolynomial (ι ⊕ κ) ℝ) :
    (specializePolynomialFiber p q).totalDegree ≤ q.totalDegree := by
  classical
  let v : ι ⊕ κ → MvPolynomial κ ℝ :=
    Sum.elim (fun i => MvPolynomial.C (p i)) MvPolynomial.X
  have hv : ∀ i, (v i).totalDegree ≤ 1 := by
    intro i
    cases i <;> simp [v]
  change (MvPolynomial.eval₂ MvPolynomial.C v q).totalDegree ≤ q.totalDegree
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  calc
    (MvPolynomial.C (q.coeff d) * ∏ i ∈ d.support, v i ^ d i).totalDegree
        ≤ (MvPolynomial.C (q.coeff d)).totalDegree +
          (∏ i ∈ d.support, v i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ d.support, v i ^ d i).totalDegree := by simp
    _ ≤ ∑ i ∈ d.support, (v i ^ d i).totalDegree := MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
      (MvPolynomial.totalDegree_pow (v i) (d i)).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _ ≤ q.totalDegree := MvPolynomial.le_totalDegree hd

end PaperI
