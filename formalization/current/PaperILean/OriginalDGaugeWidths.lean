import PaperILean.DGaugeWidthCalculus
import PaperILean.OriginalDGaugeMultiplyback

/-! I1541: six raw widths of the actual relative moving-gauge path.
The amplitudes are the source suprema before taking maxima with one.
Only original path derivatives and original rate bounds are hypotheses. -/

noncomputable section
namespace PaperI.OriginalDGaugeWidths

open PaperI.OriginalDGauge PaperI.OriginalDGaugeMultiplyback

/-- The corrected A rate of the actual original derivative. -/
def correctedA (g v : ℝ → Fin 6 → ℝ) (dbeta : ℝ → ℝ) (t : ℝ) : ℝ :=
  originalAffineBodyCoordinates (g t) (v t) 0 + dbeta t

/-- The corrected terminal rate of the actual original derivative. -/
def correctedF (g v : ℝ → Fin 6 → ℝ) (deta : ℝ → ℝ) (t : ℝ) : ℝ :=
  originalAffineBodyCoordinates (g t) (v t) 5 - deta t

/-- The literal supremum of absolute rates on the same source parameter set. -/
def rateSup (S : Set ℝ) (f : ℝ → ℝ) : ℝ := sSup ((fun t => |f t|) '' S)

def rawU (H : ℝ) (S : Set ℝ) (g v : ℝ → Fin 6 → ℝ) (dbeta : ℝ → ℝ) : ℝ :=
  H * rateSup S (correctedA g v dbeta)

def rawW (H : ℝ) (S : Set ℝ) (g v : ℝ → Fin 6 → ℝ) (deta : ℝ → ℝ) : ℝ :=
  H * rateSup S (correctedF g v deta)

private theorem rateSup_bounds (S : Set ℝ) (f : ℝ → ℝ) (t0 D : ℝ)
    (ht0 : t0 ∈ S) (hD : ∀ t ∈ S, |f t| ≤ D) :
    0 ≤ rateSup S f ∧ ∀ t ∈ S, |f t| ≤ rateSup S f := by
  have hbounded : BddAbove ((fun t => |f t|) '' S) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hD t ht
  have hbound (t : ℝ) (ht : t ∈ S) : |f t| ≤ rateSup S f :=
    le_csSup hbounded ⟨t, ht, rfl⟩
  exact ⟨(abs_nonneg _).trans (hbound t0 ht0), hbound⟩

/-- Exact raw bounds, with the mixed-rate bound derived from original body components.
The original path, actual moving gauge and literal suprema are retained. -/
theorem actual_d_gauge_raw_widths
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H B Db De : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H)
    (hg : ∀ t ∈ S, HasDerivAt g (v t) t)
    (hb : ∀ t ∈ S, HasDerivAt beta (dbeta t) t)
    (he : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (hbeta : ∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4)
    (hD : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ B)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    let u := rawU H S g v dbeta
    let w := rawW H S g v deta
    0 ≤ u ∧ 0 ≤ w ∧ ∀ t ∈ S,
      |gaugedRelativePath g beta eta t0 t 0| ≤ u ∧
      |gaugedRelativePath g beta eta t0 t 1| ≤ H*u ∧
      |gaugedRelativePath g beta eta t0 t 2| ≤ H*(B+B^2+u*w) ∧
      |gaugedRelativePath g beta eta t0 t 3| ≤ H ∧
      |gaugedRelativePath g beta eta t0 t 4| ≤ H*w ∧
      |gaugedRelativePath g beta eta t0 t 5| ≤ w := by
  have hAbound : ∀ t ∈ S, |correctedA g v dbeta t| ≤ B+Db := by
    intro t ht
    exact (abs_add _ _).trans (add_le_add (hbody t ht 0) (hdb t ht))
  have hFbound : ∀ t ∈ S, |correctedF g v deta t| ≤ B+De := by
    intro t ht
    exact (abs_sub _ _).trans (add_le_add (hbody t ht 5) (hde t ht))
  have hA := rateSup_bounds S (correctedA g v dbeta) t0 (B+Db) ht0 hAbound
  have hF := rateSup_bounds S (correctedF g v deta) t0 (B+De) ht0 hFbound
  let T : ℝ → ℝ := fun t => originalAffineBodyCoordinates (g t) (v t) 2 -
    originalAffineBodyCoordinates (g t) (v t) 1 * originalAffineBodyCoordinates (g t) (v t) 4
  have hT : ∀ t ∈ S, |T t| ≤ B+B^2 := by
    intro t ht
    have hm : |originalAffineBodyCoordinates (g t) (v t) 1 *
        originalAffineBodyCoordinates (g t) (v t) 4| ≤ B^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (hbody t ht 1) (hbody t ht 4) (abs_nonneg _) hB
    exact (abs_sub _ _).trans (add_le_add (hbody t ht 2) hm)
  let q := gaugedRelativePath g beta eta t0
  have hq : ∀ t ∈ S, HasDerivAt q
      (originalUpperBodyVelocity (q t)
        ![correctedA g v dbeta t,0,T t,1,0,correctedF g v deta t]) t := by
    intro t ht
    have hgauge := (actual_d_gauge_stage g (v t) beta eta t (dbeta t) (deta t)
      (hg t ht) (hb t ht) (he t ht) (hbeta t ht) (heta t ht) (hD t ht)).2.1
    have hrelative := originalUpperRelativeFrame_hasDerivAt (gaugedPath g beta eta)
      (gaugedPath g beta eta t0)
      (gaugeBodyRates (originalAffineBodyCoordinates (g t) (v t)) (dbeta t) (deta t)) t hgauge
    simpa only [q,gaugedRelativePath,gaugeBodyRates,correctedA,correctedF,T] using hrelative
  have hzero : q t0 = 0 := gaugedRelativePath_anchor g beta eta t0
  have hw := DGaugeWidthCalculus.gauged_coordinate_bounds q
    (correctedA g v dbeta) T (correctedF g v deta) S t0 H
    (rateSup S (correctedA g v dbeta)) (rateSup S (correctedF g v deta)) (B+B^2)
    hS ht0 hH hspan hzero hq hA.1 hF.1 (add_nonneg hB (sq_nonneg B)) hA.2 hF.2 hT
  exact ⟨mul_nonneg hH hA.1, mul_nonneg hH hF.1, hw⟩

/-- Uniform source P-power bound, with B>=1 obtained from the original D rate. -/
theorem actual_d_gauge_widths_stage
    (g v : ℝ → Fin 6 → ℝ) (beta eta dbeta deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H P C Db De : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H)
    (hg : ∀ t ∈ S, HasDerivAt g (v t) t)
    (hb : ∀ t ∈ S, HasDerivAt beta (dbeta t) t)
    (he : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (hbeta : ∀ t ∈ S, beta t = originalAffineBodyCoordinates (g t) (v t) 1)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (v t) 4)
    (hD : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (v t) 3 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) (v t) i| ≤ P^C)
    (hdb : ∀ t ∈ S, |dbeta t| ≤ Db) (hde : ∀ t ∈ S, |deta t| ≤ De) :
    let u := rawU H S g v dbeta
    let w := rawW H S g v deta
    0 ≤ u ∧ 0 ≤ w ∧ ∀ t ∈ S,
      |gaugedRelativePath g beta eta t0 t 0| ≤ P^(2*C+2)*u ∧
      |gaugedRelativePath g beta eta t0 t 1| ≤ P^(2*C+2)*(H*u) ∧
      |gaugedRelativePath g beta eta t0 t 2| ≤ P^(2*C+2)*(H*(1+u*w)) ∧
      |gaugedRelativePath g beta eta t0 t 3| ≤ P^(2*C+2)*H ∧
      |gaugedRelativePath g beta eta t0 t 4| ≤ P^(2*C+2)*(H*w) ∧
      |gaugedRelativePath g beta eta t0 t 5| ≤ P^(2*C+2)*w := by
  have hPpos : 0 < P := by linarith
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hB1 : 1 ≤ P^C := by simpa [hD t0 ht0] using hbody t0 ht0 3
  have hB0 : 0 ≤ P^C := zero_le_one.trans hB1
  obtain ⟨hu,hw,hraw⟩ := actual_d_gauge_raw_widths g v beta eta dbeta deta S t0 H (P^C) Db De
    hS ht0 hH0 hB0 hspan hg hb he hbeta heta hD hbody hdb hde
  let u := rawU H S g v dbeta
  let w := rawW H S g v deta
  have hpower : P^(2*C+2) = (P^C)^2 * P^2 := by
    rw [show 2*C+2 = C*2+2 by ring, Real.rpow_add hPpos,
      Real.rpow_mul hPpos.le, Real.rpow_two, Real.rpow_two]
  have hP2 : 1 ≤ P^2 := by nlinarith
  have hB2 : 1 ≤ (P^C)^2 := by nlinarith [sq_nonneg (P^C-1)]
  have hR1 : 1 ≤ P^(2*C+2) := by
    rw [hpower]
    exact one_le_mul_of_one_le_of_one_le hB2 hP2
  have hM : P^C+(P^C)^2 ≤ P^(2*C+2) := by
    rw [hpower]
    have htwo : (2:ℝ) ≤ P^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left htwo (sq_nonneg (P^C))
    nlinarith [sq_nonneg (P^C-1)]
  refine ⟨hu,hw,?_⟩
  intro t ht
  obtain ⟨ha,hb',hc,hd,he',hf⟩ := hraw t ht
  have hu0 : 0 ≤ u := hu
  have hw0 : 0 ≤ w := hw
  have huw : 0 ≤ u*w := mul_nonneg hu0 hw0
  have hcu : H*(P^C+(P^C)^2+u*w) ≤ P^(2*C+2)*(H*(1+u*w)) := by
    have hs : P^C+(P^C)^2+u*w ≤ P^(2*C+2)*(1+u*w) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR1) huw]
    nlinarith [mul_le_mul_of_nonneg_left hs hH0]
  refine ⟨ha.trans ?_,hb'.trans ?_,hc.trans hcu,hd.trans ?_,he'.trans ?_,hf.trans ?_⟩
  · exact le_mul_of_one_le_left hu0 hR1
  · exact le_mul_of_one_le_left (mul_nonneg hH0 hu0) hR1
  · exact le_mul_of_one_le_left hH0 hR1
  · exact le_mul_of_one_le_left (mul_nonneg hH0 hw0) hR1
  · exact le_mul_of_one_le_left hw0 hR1

end PaperI.OriginalDGaugeWidths
