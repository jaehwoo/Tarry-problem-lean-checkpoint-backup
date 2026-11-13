import PaperILean.LocalNonautonomousODE
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace PaperI.BoundedCharacteristic

abbrev Plane := ℝ × ℝ

def point (y : ℝ → ℝ) (z t : ℝ) : Plane := (y t,z+t)

def window (T : ℝ) : Set ℝ := Icc (-T) T

private theorem zero_mem_window {T : ℝ} (hT : 0 ≤ T) : 0 ∈ window T := by
  exact ⟨neg_nonpos.mpr hT,hT⟩

private theorem integral_derivWithin_window {T : ℝ} (hT : 0 ≤ T) {A : ℝ → ℝ}
    (hA : ContinuousOn A (window T)) {t : ℝ} (ht : t ∈ window T) :
    HasDerivWithinAt (fun t => ∫ s in (0 : ℝ)..t, A s) (A t) (window T) t := by
  let A' := fun s => A (projIcc (-T) T (by linarith) s)
  have hc : Continuous A' :=
    (continuousOn_iff_continuous_restrict.mp hA).comp continuous_projIcc
  have heq : EqOn A A' (window T) := by
    intro s hs
    have hs' : s ∈ Icc (-T) T := hs
    rw [show A' s = A (projIcc (-T) T (by linarith) s) from rfl, projIcc_of_mem _ hs']
  have hder : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, A' s) (A' t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [← heq ht] at hder
  apply hder.hasDerivWithinAt.congr
  · intro s hs
    exact intervalIntegral.integral_congr fun r hr => heq (uIcc_subset_Icc (zero_mem_window hT) hs hr)
  · exact intervalIntegral.integral_congr fun r hr => heq (uIcc_subset_Icc (zero_mem_window hT) ht hr)

theorem exponential_solution_window {T : ℝ} (hT : 0 ≤ T) {A w : ℝ → ℝ}
    (hA : ContinuousOn A (window T))
    (hw : ∀ t ∈ window T, HasDerivWithinAt w (A t * w t) (window T) t)
    {t : ℝ} (ht : t ∈ window T) :
    w t = w 0 * Real.exp (∫ s in (0 : ℝ)..t, A s) := by
  let q := fun t => w t * Real.exp (- ∫ s in (0 : ℝ)..t, A s)
  have hd : ∀ s ∈ window T, HasDerivWithinAt q 0 (window T) s := by
    intro s hs
    convert (hw s hs).mul (integral_derivWithin_window hT hA hs).neg.exp using 1
    ring
  have hc : ContinuousOn q (window T) := fun s hs => (hd s hs).continuousWithinAt
  have heq : q t = q 0 := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hc.mono (uIcc_subset_Icc (zero_mem_window hT) ht))
      (f' := fun _ => (0 : ℝ))
      (by
        intro s hs
        have hsn : window T ∈ 𝓝 s :=
          Icc_mem_nhds (lt_of_le_of_lt (le_min (neg_nonpos.mpr hT) ht.1) hs.1)
            (lt_of_lt_of_le hs.2 (max_le hT ht.2))
        exact ((hd s (mem_of_mem_nhds hsn)).hasDerivAt hsn).hasDerivWithinAt)
      (continuous_const.intervalIntegrable 0 t)
    apply sub_eq_zero.mp
    simpa using hi.symm
  change w t * Real.exp (- ∫ s in (0 : ℝ)..t, A s) = w 0 * Real.exp (- ∫ s in (0:ℝ)..0, A s) at heq
  rw [Real.exp_neg] at heq
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at heq
  exact (div_eq_iff (Real.exp_ne_zero _)).mp (by simpa only [div_eq_mul_inv] using heq)

theorem exponential_derivative_window {T : ℝ} (hT : 0 ≤ T) {A : ℝ → ℝ}
    (hA : ContinuousOn A (window T)) {t : ℝ} (ht : t ∈ window T) :
    HasDerivWithinAt (fun t => Real.exp (∫ s in (0 : ℝ)..t, A s))
      (A t * Real.exp (∫ s in (0 : ℝ)..t, A s)) (window T) t := by
  simpa only [mul_comm] using (integral_derivWithin_window hT hA ht).exp

theorem exponential_bounds {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hsmall : L*T ≤ Real.log 2) {A : ℝ → ℝ}
    (hA : ∀ t ∈ window T, |A t| ≤ L) {t : ℝ} (ht : t ∈ window T) :
    let J := Real.exp (∫ s in (0 : ℝ)..t, A s)
    1/2 ≤ J ∧ J ≤ 2 ∧ 1/2 ≤ J⁻¹ ∧ J⁻¹ ≤ 2 := by
  have habs : |∫ s in (0 : ℝ)..t, A s| ≤ Real.log 2 := by
    calc
      |∫ s in (0 : ℝ)..t, A s| ≤ L * |t| := by
        have hbound : ∀ s ∈ uIoc (0 : ℝ) t, ‖A s‖ ≤ L := by
          intro s hs
          rw [Real.norm_eq_abs]
          exact hA s (uIcc_subset_Icc (zero_mem_window hT) ht (uIoc_subset_uIcc hs))
        simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ L * T := mul_le_mul_of_nonneg_left (abs_le.mpr ht) hL
      _ ≤ _ := hsmall
  have hlow : Real.exp (-Real.log 2) = 1/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hhigh : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  dsimp only
  rw [← Real.exp_neg]
  exact ⟨hlow ▸ Real.exp_le_exp.mpr (abs_le.mp habs).1,
    hhigh ▸ Real.exp_le_exp.mpr (abs_le.mp habs).2,
    hlow ▸ Real.exp_le_exp.mpr (by linarith [(abs_le.mp habs).2]),
    hhigh ▸ Real.exp_le_exp.mpr (by linarith [(abs_le.mp habs).1])⟩

def differenceCoefficient (u : Plane → ℝ) (y w : ℝ → ℝ) (z t : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1, u (y t + r*w t,z+t)

theorem differenceCoefficient_continuousOn {T : ℝ}
    {D : Set Plane} {u : Plane → ℝ} (hu : ContinuousOn u D)
    {y w : ℝ → ℝ} {z : ℝ} (hy : ContinuousOn y (window T)) (hw : ContinuousOn w (window T))
    (hmem : ∀ t ∈ window T, ∀ r ∈ Icc (0:ℝ) 1, (y t+r*w t,z+t) ∈ D) :
    ContinuousOn (differenceCoefficient u y w z) (window T) := by
  rw [continuousOn_iff_continuous_restrict]
  let pr := fun r : ℝ => (projIcc (0:ℝ) 1 (by norm_num) r : ℝ)
  let H := fun (t : window T) (r : ℝ) => u (y t + pr r * w t,z+t)
  have hH : Continuous H.uncurry := by
    apply hu.comp_continuous
    · have hy' := (continuousOn_iff_continuous_restrict.mp hy).comp
          (continuous_fst : Continuous (Prod.fst : window T × ℝ → window T))
      have hw' := (continuousOn_iff_continuous_restrict.mp hw).comp
          (continuous_fst : Continuous (Prod.fst : window T × ℝ → window T))
      have hr : Continuous (fun p : window T × ℝ => pr p.2) :=
        continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
      exact (hy'.add (hr.mul hw')).prodMk
        (continuous_const.add (continuous_subtype_val.comp continuous_fst))
    · intro p
      exact hmem p.1 p.1.2 (pr p.2) (projIcc (0:ℝ) 1 (by norm_num) p.2).2
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hH 0 1).congr
  intro t
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0:ℝ) 1 := by simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hr
  have hp : pr r = r :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hr')
  change u (y t + pr r*w t,z+t) = u (y t+r*w t,z+t)
  rw [hp]

theorem horizontal_difference {D : Set Plane} {d u : Plane → ℝ} {a z w : ℝ}
    (hu : ContinuousOn u D)
    (hdu : ∀ p ∈ D, HasDerivAt (fun x => d (x,p.2)) (u p) p.1)
    (hmem : ∀ r ∈ Icc (0:ℝ) 1, (a+r*w,z) ∈ D) :
    d (a+w,z)-d (a,z) = (∫ r in (0:ℝ)..1, u (a+r*w,z))*w := by
  have hc : ContinuousOn (fun r : ℝ => u (a+r*w,z)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hu.comp (by fun_prop) hmem
  have hd : ∀ r ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun r => d (a+r*w,z)) (w*u (a+r*w,z)) r := by
    intro r hr
    have hr' := (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)) ▸ hr
    have he : HasDerivAt (fun r : ℝ => a+r*w) w r := by
      simpa using ((hasDerivAt_id r).mul_const w).const_add a
    simpa [Function.comp_def] using (hdu (a+r*w,z) (hmem r hr')).scomp r he
  have hi : IntervalIntegrable (fun r => w*u (a+r*w,z)) volume 0 1 :=
    (continuousOn_const.mul hc).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at he
  simpa [mul_comm] using he.symm

end PaperI.BoundedCharacteristic
