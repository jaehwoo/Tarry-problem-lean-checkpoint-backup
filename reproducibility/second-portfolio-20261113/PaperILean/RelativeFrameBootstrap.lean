import PaperILean.RelativeFrameCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! I298: simultaneous continuation of the relative frame and its inverse.
A linear barrier supplies the strict bootstrap margin; the mean-value estimate
then integrates the original derivative bound. No time-dependent exponential
formula, commutation, or differentiability of a norm is presumed. -/
noncomputable section
open Set
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem norm_bootstrap_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (q : ℝ) (hq : 0 ≤ q) (hsmall : q ≤ 1 / 8)
    (hinit : ‖f 0‖ ≤ 1)
    (hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ 2 → ‖f' t‖ ≤ 4 * q) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ 7 / 4 ∧ ‖f t - f 0‖ ≤ 4 * q * t := by
  have hbar : ∀ t : ℝ, HasDerivAt (fun u : ℝ => 1 + (3 / 4 : ℝ) * u) (3 / 4) t := by
    intro t
    simpa using ((hasDerivAt_id t).const_mul (3 / 4 : ℝ)).const_add 1
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ 1 + (3 / 4 : ℝ) * t := by
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simpa using hinit) hbar
    intro t ht heq
    have hn : ‖f t‖ ≤ 2 := by rw [heq]; linarith [ht.2]
    have hb := hbound t (Ico_subset_Icc_self ht) hn
    linarith
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f' t‖ ≤ 4 * q := by
    intro t ht
    apply hbound t ht
    have hh := hf t ht
    linarith [ht.2]
  intro t ht
  constructor
  · have hh := hf t ht; linarith [ht.2]
  · simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (hder u hu).hasDerivWithinAt)
      (fun u hu => hb u (Ico_subset_Icc_self hu)) t ht

theorem relativeFrame_bootstrap
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (q : ℝ) (hq : 0 ≤ q) (hsmall : q ≤ 1 / 8)
    (hinit : A 0 = 1) (hu : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (A t))
    (hgen : ∀ t ∈ Icc (0 : ℝ) 1, ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      HasDerivAt A (A t * S) t ∧ ‖S‖ ≤ q * ‖(A t)⁻¹‖) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖A t‖ ≤ 7 / 4 ∧ ‖(A t)⁻¹‖ ≤ 7 / 4 ∧
      ‖A t - 1‖ ≤ 4 * q * t ∧ ‖(A t)⁻¹ - 1‖ ≤ 4 * q * t := by
  let f : ℝ → Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ := fun t => (A t, (A t)⁻¹)
  let f' : ℝ → Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ :=
    fun t => (deriv A t, deriv (fun u => (A u)⁻¹) t)
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    obtain ⟨S, hS, _⟩ := hgen t ht
    exact hS.differentiableAt.hasDerivAt.prodMk
      (hasDerivAt_inverse_horizontal hS (hu t ht)).differentiableAt.hasDerivAt
  have hi : ‖f 0‖ ≤ 1 := by simp [f, hinit]
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ 2 → ‖f' t‖ ≤ 4 * q := by
    intro t ht hn
    obtain ⟨S, hS, hs⟩ := hgen t ht
    have hInv := hasDerivAt_inverse_horizontal hS (hu t ht)
    have hnorm : ‖A t‖ ≤ 2 ∧ ‖(A t)⁻¹‖ ≤ 2 := by
      simpa only [f, Prod.norm_def, max_le_iff] using hn
    have hs' : ‖S‖ ≤ 2 * q := by nlinarith [hnorm.2]
    change max ‖deriv A t‖ ‖deriv (fun u => (A u)⁻¹) t‖ ≤ 4 * q
    rw [hS.deriv, hInv.deriv, neg_mul, norm_neg]
    apply max_le
    · calc
        ‖A t * S‖ ≤ ‖A t‖ * ‖S‖ := norm_mul_le _ _
        _ ≤ 2 * (2 * q) := mul_le_mul hnorm.1 hs' (norm_nonneg _) (by positivity)
        _ = 4 * q := by ring
    · calc
        ‖S * (A t)⁻¹‖ ≤ ‖S‖ * ‖(A t)⁻¹‖ := norm_mul_le _ _
        _ ≤ (2 * q) * 2 := mul_le_mul hs' hnorm.2 (norm_nonneg _) (by positivity)
        _ = 4 * q := by ring
  intro t ht
  obtain ⟨h1, h2⟩ := norm_bootstrap_Icc f f' q hq hsmall hi hd hb t ht
  have h1' : ‖A t‖ ≤ 7 / 4 ∧ ‖(A t)⁻¹‖ ≤ 7 / 4 := by
    simpa only [f, Prod.norm_def, max_le_iff] using h1
  have h2' : ‖A t - 1‖ ≤ 4 * q * t ∧ ‖(A t)⁻¹ - 1‖ ≤ 4 * q * t := by
    simpa only [f, hinit, inv_one, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      max_le_iff] using h2
  exact ⟨h1'.1, h1'.2, h2'⟩

end PaperI
