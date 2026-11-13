import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Amplitude normalization for the same centerline in I1263. The original
function `h` remains the geometric centerline. Subtracting its value at a
specified point only supplies a bounded scalar for preparation. Positive
iterated derivatives agree, while order zero is deliberately not identified.
These lemmas do not supply regular pieces, derivative format, a good set,
or strip area. The offset obstruction is recorded in checkpoint 127's review. -/

noncomputable section
namespace PaperI
open Set

theorem centered_lipschitz_amplitude
    {h : ℝ → ℝ} {a b q₀ q : ℝ} {K : NNReal}
    (hLip : LipschitzOnWith K h (Icc a b))
    (hq₀ : q₀ ∈ Icc a b) (hq : q ∈ Icc a b) :
    |h q - h q₀| ≤ (K : ℝ) * (b - a) := by
  have hdist : |q - q₀| ≤ b - a := by
    apply abs_le.mpr
    constructor <;> linarith [hq₀.1, hq₀.2, hq.1, hq.2]
  calc
    |h q - h q₀| ≤ (K : ℝ) * |q - q₀| := by
      simpa only [Real.dist_eq] using hLip.dist_le_mul q hq q₀ hq₀
    _ ≤ (K : ℝ) * (b - a) := mul_le_mul_of_nonneg_left hdist K.coe_nonneg

theorem centered_one_lipschitz_amplitude
    {h : ℝ → ℝ} {a b q₀ q : ℝ}
    (hLip : LipschitzOnWith 1 h (Icc a b))
    (hq₀ : q₀ ∈ Icc a b) (hq : q ∈ Icc a b) :
    |h q - h q₀| ≤ b - a := by
  simpa using centered_lipschitz_amplitude hLip hq₀ hq

theorem centered_contDiffOn {h : ℝ → ℝ} {s : Set ℝ} {n : WithTop ENat}
    (hsmooth : ContDiffOn ℝ n h s) (q₀ : ℝ) :
    ContDiffOn ℝ n (fun q => h q - h q₀) s := by
  exact hsmooth.sub contDiffOn_const

/-- Constant translation preserves positive iterated derivatives even before
regularity is supplied. This identity does not assert derivative existence.
For actual derivatives on a regular piece use `centered_contDiffOn`. -/
theorem iteratedDeriv_centered (h : ℝ → ℝ) (q₀ q : ℝ) (j : ℕ)
    (hj : 0 < j) :
    iteratedDeriv j (fun x => h x - h q₀) q = iteratedDeriv j h q := by
  simpa only [sub_eq_add_neg, add_comm] using
    (iteratedDeriv_const_add (f := h) (x := q) hj (-h q₀))

end PaperI
