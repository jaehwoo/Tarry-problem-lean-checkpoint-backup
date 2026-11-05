import PaperILean.OriginalUpperBodyFlow
import Mathlib.Analysis.Calculus.MeanValue

/-! The coordinate integration needed for I1574. The six genuine derivatives
are integrated on one convex parameter set from an anchor in that set. The
domain need not contain its boundary, and the anchor may have either orientation.
No integrability, endpoint continuity or coordinate bound is assumed. -/

noncomputable section
namespace PaperI.FGaugeWidthCalculus
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

/-- Successive integration of the actual terminal-chart triangular ODE.
The parameter Dmax is a bound for the corrected D rate; the source wrapper
supplies its literal supremum. Division by H and bounded comparisons occur
only in the subsequent box theorem. -/
theorem gauged_coordinate_bounds
    (q : ℝ → Fin 6 → ℝ) (A Z D : ℝ → ℝ) (S : Set ℝ)
    (t0 H Dmax M : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 0 ≤ H)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H) (hzero : q t0 = 0)
    (hq : ∀ t ∈ S, HasDerivAt q
      (originalUpperBodyVelocity (q t) ![A t,Z t,0,D t,0,1]) t)
    (hDmax : 0 ≤ Dmax) (hM : 0 ≤ M)
    (hA : ∀ t ∈ S, |A t| ≤ M)
    (hZ : ∀ t ∈ S, |Z t| ≤ M)
    (hD : ∀ t ∈ S, |D t| ≤ Dmax) :
    ∀ t ∈ S,
      |q t 0| ≤ H*M ∧
      |q t 1| ≤ M*(H^2*Dmax+H) ∧
      |q t 2| ≤ H*M*(H^2*Dmax+H) ∧
      |q t 3| ≤ H*Dmax ∧
      |q t 4| ≤ H^2*Dmax ∧
      |q t 5| ≤ H := by
  have hzeroi (i : Fin 6) : q t0 i = 0 := by
    simpa using congrFun hzero i
  have ha : ∀ t ∈ S, |q t 0| ≤ H*M :=
    anchored_scalar_bound (fun t => q t 0) A S t0 H M hS ht0 (hzeroi 0)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (0 : Fin 6))
      hM hA hspan
  have hd : ∀ t ∈ S, |q t 3| ≤ H*Dmax :=
    anchored_scalar_bound (fun t => q t 3) D S t0 H Dmax hS ht0 (hzeroi 3)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (3 : Fin 6))
      hDmax hD hspan
  have hf : ∀ t ∈ S, |q t 5| ≤ H := by
    have h := anchored_scalar_bound (fun t => q t 5) (fun _ => 1) S t0 H 1
      hS ht0 (hzeroi 5)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (5 : Fin 6))
      (by norm_num) (by intro t ht; norm_num) hspan
    simpa using h
  have hb : ∀ t ∈ S, |q t 1| ≤ M*(H^2*Dmax+H) := by
    have h := anchored_scalar_bound (fun t => q t 1)
      (fun t => Z t+q t 0*D t) S t0 H (M+(H*M)*Dmax)
      hS ht0 (hzeroi 1)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (1 : Fin 6))
      (by positivity)
      (by
        intro t ht
        calc
          |Z t+q t 0*D t| ≤ |Z t|+|q t 0*D t| := abs_add _ _
          _ = |Z t| + |q t 0| * |D t| := by rw [abs_mul]
          _ ≤ M+(H*M)*Dmax :=
            add_le_add (hZ t ht)
              (mul_le_mul (ha t ht) (hD t ht) (abs_nonneg _) (mul_nonneg hH hM)))
      hspan
    intro t ht
    calc
      |q t 1| ≤ H*(M+(H*M)*Dmax) := h t ht
      _ = M*(H^2*Dmax+H) := by ring
  have he : ∀ t ∈ S, |q t 4| ≤ H^2*Dmax := by
    have h := anchored_scalar_bound (fun t => q t 4) (fun t => q t 3)
      S t0 H (H*Dmax) hS ht0 (hzeroi 4)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (4 : Fin 6))
      (mul_nonneg hH hDmax) hd hspan
    intro t ht
    calc
      |q t 4| ≤ H*(H*Dmax) := h t ht
      _ = H^2*Dmax := by ring
  have hc : ∀ t ∈ S, |q t 2| ≤ H*M*(H^2*Dmax+H) := by
    have h := anchored_scalar_bound (fun t => q t 2) (fun t => q t 1)
      S t0 H (M*(H^2*Dmax+H)) hS ht0 (hzeroi 2)
      (by
        intro t ht
        simpa [originalUpperBodyVelocity] using hasDerivAt_pi.mp (hq t ht) (2 : Fin 6))
      (by positivity) hb hspan
    intro t ht
    calc
      |q t 2| ≤ H*(M*(H^2*Dmax+H)) := h t ht
      _ = H*M*(H^2*Dmax+H) := by ring
  exact fun t ht => ⟨ha t ht,hb t ht,hc t ht,hd t ht,he t ht,hf t ht⟩

end PaperI.FGaugeWidthCalculus
