import PaperILean.OriginalUpperBodyFlow
import Mathlib.Analysis.Calculus.MeanValue

/-! Necessary coordinate integration bounds for I1541.
The actual-source wrapper supplies the ODE from the proved moving gauge.
The convex domain need not contain its boundary, and either anchor orientation
is allowed. No integral or endpoint-continuity premise is introduced. -/

noncomputable section
namespace PaperI.DGaugeWidthCalculus
open Set

private theorem anchored_scalar_bound
    (f f' : ℝ → ℝ) (S : Set ℝ) (t0 H K : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hzero : f t0 = 0)
    (hf : ∀ t ∈ S, HasDerivAt f (f' t) t) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ S, |f' t| ≤ K)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H) :
    ∀ t ∈ S, |f t| ≤ H*K := by
  intro t ht
  have h := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hf s hs).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs) ht0 ht
  calc
    |f t| ≤ K*|t-t0| := by simpa only [hzero, sub_zero, Real.norm_eq_abs] using h
    _ ≤ K*H := mul_le_mul_of_nonneg_left (hspan t ht) hK
    _ = H*K := mul_comm _ _

/-- The six raw anisotropic widths follow successively from the triangular
coordinate equations. In particular no maximum with one is taken here. -/
theorem gauged_coordinate_bounds
    (q : ℝ → Fin 6 → ℝ) (A T F : ℝ → ℝ) (S : Set ℝ)
    (t0 H Amax Fmax M : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 0 ≤ H)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H) (hzero : q t0 = 0)
    (hq : ∀ t ∈ S, HasDerivAt q
      (originalUpperBodyVelocity (q t) ![A t,0,T t,1,0,F t]) t)
    (hAmax : 0 ≤ Amax) (hFmax : 0 ≤ Fmax) (hM : 0 ≤ M)
    (hA : ∀ t ∈ S, |A t| ≤ Amax)
    (hF : ∀ t ∈ S, |F t| ≤ Fmax)
    (hT : ∀ t ∈ S, |T t| ≤ M) :
    ∀ t ∈ S,
      |q t 0| ≤ H*Amax ∧
      |q t 1| ≤ H*(H*Amax) ∧
      |q t 2| ≤ H*(M+(H*Amax)*(H*Fmax)) ∧
      |q t 3| ≤ H ∧
      |q t 4| ≤ H*(H*Fmax) ∧
      |q t 5| ≤ H*Fmax := by
  have hzeroi (i : Fin 6) : q t0 i = 0 := by
    simpa using congrFun hzero i
  have ha : ∀ t ∈ S, |q t 0| ≤ H*Amax :=
    anchored_scalar_bound (fun t => q t 0) A S t0 H Amax hS ht0 (hzeroi 0)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (0 : Fin 6))
      hAmax hA hspan
  have hd : ∀ t ∈ S, |q t 3| ≤ H := by
    have h := anchored_scalar_bound (fun t => q t 3) (fun _ => 1) S t0 H 1
      hS ht0 (hzeroi 3)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (3 : Fin 6))
      (by norm_num) (by intro t ht; norm_num) hspan
    simpa using h
  have hf : ∀ t ∈ S, |q t 5| ≤ H*Fmax :=
    anchored_scalar_bound (fun t => q t 5) F S t0 H Fmax hS ht0 (hzeroi 5)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (5 : Fin 6))
      hFmax hF hspan
  have hb : ∀ t ∈ S, |q t 1| ≤ H*(H*Amax) :=
    anchored_scalar_bound (fun t => q t 1) (fun t => q t 0) S t0 H (H*Amax)
      hS ht0 (hzeroi 1)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (1 : Fin 6))
      (mul_nonneg hH hAmax) ha hspan
  have he : ∀ t ∈ S, |q t 4| ≤ H*(H*Fmax) :=
    anchored_scalar_bound (fun t => q t 4) (fun t => q t 3*F t) S t0 H (H*Fmax)
      hS ht0 (hzeroi 4)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (4 : Fin 6))
      (mul_nonneg hH hFmax)
      (by
        intro t ht
        rw [abs_mul]
        exact mul_le_mul (hd t ht) (hF t ht) (abs_nonneg _) hH)
      hspan
  have hc : ∀ t ∈ S, |q t 2| ≤ H*(M+(H*Amax)*(H*Fmax)) :=
    anchored_scalar_bound (fun t => q t 2) (fun t => T t+q t 1*F t) S t0 H
      (M+(H*Amax)*(H*Fmax)) hS ht0 (hzeroi 2)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (2 : Fin 6))
      (add_nonneg hM (mul_nonneg (mul_nonneg hH hAmax) (mul_nonneg hH hFmax)))
      (by
        intro t ht
        calc
          |T t+q t 1*F t| ≤ |T t|+|q t 1*F t| := abs_add _ _
          _ = |T t| + |q t 1| * |F t| := by rw [abs_mul]
          _ ≤ M+(H*(H*Amax))*Fmax :=
            add_le_add (hT t ht)
              (mul_le_mul (hb t ht) (hF t ht) (abs_nonneg _)
                (mul_nonneg hH (mul_nonneg hH hAmax)))
          _ = M+(H*Amax)*(H*Fmax) := by ring)
      hspan
  exact fun t ht => ⟨ha t ht,hb t ht,hc t ht,hd t ht,he t ht,hf t ht⟩

end PaperI.DGaugeWidthCalculus
