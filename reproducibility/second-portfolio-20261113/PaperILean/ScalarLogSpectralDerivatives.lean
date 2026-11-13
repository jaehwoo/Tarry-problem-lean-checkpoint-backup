import PaperILean.SpectralCothKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar ingredients of the symmetric-space spectral Hessian (source214-223).
The collision coefficient is the actual scalar second derivative. These results
do not assert a matrix Frechet derivative or differentiability of an eigenbasis.
-/

noncomputable section
open Filter
open scoped Topology
namespace PaperI

def logSquareFirst (s : ℝ) : ℝ := 2 * Real.log s / s

def logSquareSecond (s : ℝ) : ℝ := 2 * (1 - Real.log s) / s ^ 2

def logSquareDividedDifference (x y : ℝ) : ℝ :=
  if x = y then logSquareSecond x else (logSquareFirst x - logSquareFirst y) / (x - y)

theorem hasDerivAt_logSquare (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => (Real.log x) ^ 2) (logSquareFirst s) s := by
  convert (Real.hasDerivAt_log hs.ne').pow 2 using 1
  simp only [logSquareFirst]
  field_simp

theorem hasDerivAt_logSquareFirst (s : ℝ) (hs : 0 < s) :
    HasDerivAt logSquareFirst (logSquareSecond s) s := by
  convert ((Real.hasDerivAt_log hs.ne').const_mul 2).div (hasDerivAt_id s) hs.ne' using 1
  simp only [logSquareSecond, id]
  field_simp
  ring

theorem logSquareDividedDifference_self (x : ℝ) :
    logSquareDividedDifference x x = logSquareSecond x := by
  simp [logSquareDividedDifference]

theorem logSquareDividedDifference_symm (x y : ℝ) :
    logSquareDividedDifference x y = logSquareDividedDifference y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [logSquareDividedDifference, h, Ne.symm h, if_false]
    rw [← neg_sub (logSquareFirst x) (logSquareFirst y), ← neg_sub x y, neg_div_neg_eq]

theorem continuousAt_logSquareDividedDifference_collision (x : ℝ) (hx : 0 < x) :
    ContinuousAt (logSquareDividedDifference x) x := by
  have he : logSquareDividedDifference x = Function.update
      (fun y : ℝ => (logSquareFirst y - logSquareFirst x) / (y - x)) x
      (logSquareSecond x) := by
    funext y
    by_cases h : y = x
    · subst y; simp [logSquareDividedDifference, Function.update]
    · simp only [Function.update, h, dite_false, logSquareDividedDifference, Ne.symm h, if_false]
      rw [← neg_sub (logSquareFirst y) (logSquareFirst x), ← neg_sub y x, neg_div_neg_eq]
  rw [he]
  exact (hasDerivAt_logSquareFirst x hx).continuousAt_div

theorem logSquare_diagonal_chain_coefficient (s : ℝ) (hs : 0 < s) :
    4 * s ^ 2 * logSquareSecond s + 4 * s * logSquareFirst s = 8 := by
  simp only [logSquareSecond, logSquareFirst]
  field_simp
  ring

theorem spectralCothKernel_half_difference_of_ne (a b : ℝ) (hab : a ≠ b) :
    spectralCothKernel ((a - b) / 2) =
      ((a - b) / 2) * (Real.exp a + Real.exp b) / (Real.exp a - Real.exp b) := by
  have ht : (a - b) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
  have ha : Real.exp a = Real.exp ((a + b) / 2) * Real.exp ((a - b) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hb : Real.exp b = Real.exp ((a + b) / 2) * Real.exp (-((a - b) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hr : (Real.exp a + Real.exp b) / (Real.exp a - Real.exp b) =
      ((Real.exp ((a - b) / 2) + Real.exp (-((a - b) / 2))) / 2) /
        ((Real.exp ((a - b) / 2) - Real.exp (-((a - b) / 2))) / 2) := by
    rw [ha, hb, ← mul_add, ← mul_sub,
      mul_div_mul_left _ _ (Real.exp_ne_zero _),
      div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [spectralCothKernel_of_ne_zero ht, Real.cosh_eq, Real.sinh_eq,
    mul_div_assoc, ← hr, ← mul_div_assoc]

theorem logSquare_pair_chain_coefficient (a b : ℝ) :
    8 * Real.exp a * Real.exp b * logSquareDividedDifference (Real.exp a) (Real.exp b) +
      8 * (a + b) = 16 * spectralCothKernel ((a - b) / 2) := by
  by_cases hab : a = b
  · subst b
    simp only [logSquareDividedDifference_self, sub_self, zero_div, spectralCothKernel_zero,
      logSquareSecond, Real.log_exp]
    field_simp [Real.exp_ne_zero]
    ring
  · have hxy : Real.exp a ≠ Real.exp b := fun h => hab (Real.exp_injective h)
    rw [spectralCothKernel_half_difference_of_ne a b hab]
    simp only [logSquareDividedDifference, hxy, if_false, logSquareFirst, Real.log_exp]
    field_simp [Real.exp_ne_zero a, Real.exp_ne_zero b, sub_ne_zero.mpr hxy]
    ring

end PaperI
