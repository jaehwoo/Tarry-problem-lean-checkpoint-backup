import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual derivatives and convexity for the finite nonnegative exponential sums
used in the minimizing-frame proof. Zero weights/rates and empty sums are allowed. -/
noncomputable section
open scoped BigOperators
namespace PaperI

def weightedExponentialSum {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i * Real.exp (t * a i)

theorem hasDerivAt_weightedExponentialSum {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (weightedExponentialSum s w a)
      (weightedExponentialSum s (fun i => w i * a i) a t) t := by
  unfold weightedExponentialSum
  apply HasDerivAt.sum
  intro i _
  convert (((hasDerivAt_id t).mul_const (a i)).exp.const_mul (w i)) using 1 <;> dsimp <;> ring

theorem deriv_weightedExponentialSum {ι : Type*} (s : Finset ι) (w a : ι → ℝ) :
    deriv (weightedExponentialSum s w a) = weightedExponentialSum s (fun i => w i * a i) a := by
  funext t
  exact (hasDerivAt_weightedExponentialSum s w a t).deriv

theorem hasDerivAt_deriv_weightedExponentialSum {ι : Type*}
    (s : Finset ι) (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (deriv (weightedExponentialSum s w a))
      (weightedExponentialSum s (fun i => w i * (a i) ^ 2) a t) t := by
  rw [deriv_weightedExponentialSum]
  convert hasDerivAt_weightedExponentialSum s (fun i => w i * a i) a t using 1
  unfold weightedExponentialSum
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem deriv2_weightedExponentialSum {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (t : ℝ) :
    deriv (deriv (weightedExponentialSum s w a)) t =
      weightedExponentialSum s (fun i => w i * (a i) ^ 2) a t :=
  (hasDerivAt_deriv_weightedExponentialSum s w a t).deriv

theorem weightedExponentialSum_convex {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : ConvexOn ℝ Set.univ (weightedExponentialSum s w a) := by
  apply convexOn_univ_of_deriv2_nonneg
    (fun t => (hasDerivAt_weightedExponentialSum s w a t).differentiableAt)
    (fun t => (hasDerivAt_deriv_weightedExponentialSum s w a t).differentiableAt)
  intro t
  change 0 ≤ deriv (deriv (weightedExponentialSum s w a)) t
  rw [deriv2_weightedExponentialSum]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _))
    (Real.exp_pos _).le)

end PaperI
