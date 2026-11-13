import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Identify a genuine iterated Frechet derivative with a line second
derivative. No Hessian is defined by the directional formula. -/
noncomputable section
namespace PaperI

theorem deriv2_smul_line_eq_fderiv2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ⊤ f) (H : E) :
    deriv (deriv (fun t : ℝ => f (t • H))) 0 =
      (fderiv ℝ (fderiv ℝ f) 0 H) H := by
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => u • H) H t := by
    simpa using (hasDerivAt_id t).smul_const H
  have heq : deriv (fun t : ℝ => f (t • H)) =
      fun t => fderiv ℝ f (t • H) H := by
    funext t
    exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t (hline t)).deriv
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ⊤) (by simp)).differentiable (by simp)
  have h := (hd.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 (hline 0)).clm_apply
    (hasDerivAt_const (0 : ℝ) H)
  rw [heq]
  simpa only [zero_smul, map_zero, add_zero] using h.deriv

end PaperI
