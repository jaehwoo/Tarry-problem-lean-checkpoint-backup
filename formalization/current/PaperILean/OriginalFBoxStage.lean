import PaperILean.FGaugeWidthCalculus
import PaperILean.OriginalFBox

/-! I1572, the coordinate-bound part of I1574, and I1576.
The actual original path is restored from its genuine moving f-gauge.
The two amplitudes are literal suprema of the corrected source rates.
No covering-number, smallness, nondegeneracy or model-comparison result is claimed. -/

noncomputable section
namespace PaperI.OriginalFBoxStage
open OriginalFGauge OriginalFBox

/-- Corrected D rate, relabelled delta in the source. -/
def correctedDelta (g vel : ℝ → Fin 6 → ℝ) (deta : ℝ → ℝ) (t : ℝ) : ℝ :=
  originalAffineBodyCoordinates (g t) (vel t) 3 + deta t

/-- Corrected C rate zeta; tau is the original Tx rate. -/
def correctedZeta (g vel : ℝ → Fin 6 → ℝ) (dtau : ℝ → ℝ) (t : ℝ) : ℝ :=
  originalAffineBodyCoordinates (g t) (vel t) 1 +
    originalAffineBodyCoordinates (g t) (vel t) 0 *
      originalAffineBodyCoordinates (g t) (vel t) 4 + dtau t

def rateSup (S : Set ℝ) (f : ℝ → ℝ) : ℝ := sSup ((fun t => |f t|) '' S)

def rawU (H : ℝ) (S : Set ℝ) (g vel : ℝ → Fin 6 → ℝ) (deta : ℝ → ℝ) : ℝ :=
  H^2 * rateSup S (correctedDelta g vel deta)

def rawV (H : ℝ) (S : Set ℝ) (g vel : ℝ → Fin 6 → ℝ) (dtau : ℝ → ℝ) : ℝ :=
  H * rateSup S (correctedZeta g vel dtau)

def gaugedRelativePath (g : ℝ → Fin 6 → ℝ) (tau eta : ℝ → ℝ)
    (t0 t : ℝ) : Fin 6 → ℝ :=
  originalUpperRelativeFrame (gaugedPath g tau eta t0) (gaugedPath g tau eta t)

private theorem rateSup_bounds (S : Set ℝ) (f : ℝ → ℝ) (t0 D : ℝ)
    (ht0 : t0 ∈ S) (hD : ∀ t ∈ S, |f t| ≤ D) :
    0 ≤ rateSup S f ∧ rateSup S f ≤ D ∧ ∀ t ∈ S, |f t| ≤ rateSup S f := by
  have hne : ((fun t => |f t|) '' S).Nonempty := ⟨|f t0|,t0,ht0,rfl⟩
  have hbounded : BddAbove ((fun t => |f t|) '' S) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact hD t ht
  have hpoint (t : ℝ) (ht : t ∈ S) : |f t| ≤ rateSup S f :=
    le_csSup hbounded ⟨t,ht,rfl⟩
  refine ⟨(abs_nonneg _).trans (hpoint t0 ht0),?_,hpoint⟩
  apply csSup_le hne
  rintro _ ⟨t,ht,rfl⟩
  exact hD t ht

private theorem two_comparisons_power (P C E : ℝ) (hP : 2 ≤ P) :
    16 * P^E * (P^C)^2 ≤ P^(E+2*C+4) := by
  have hPpos : 0 < P := by linarith
  have h16 : (16:ℝ) ≤ P^4 := by
    have hP2 : (4:ℝ) ≤ P^2 := by nlinarith
    nlinarith [sq_nonneg (P^2-4)]
  have heq : P^(E+2*C+4) = P^E * (P^C)^2 * P^4 := by
    rw [Real.rpow_add hPpos,Real.rpow_add hPpos,
      show 2*C=C*2 by ring,Real.rpow_mul hPpos.le,Real.rpow_two]
    exact congrArg (fun x : ℝ => P^E * (P^C)^2 * x) (Real.rpow_natCast P 4)
  rw [heq]
  nlinarith only [mul_le_mul_of_nonneg_left h16
    (mul_nonneg (Real.rpow_nonneg hPpos.le E) (sq_nonneg (P^C)))]

private theorem common_envelope_power (P C : ℝ) (hP : 2 ≤ P) (hB : 1 ≤ P^C) :
    2*((P^C)^2+2*P^C) ≤ P^(2*C+3) := by
  have hPpos : 0 < P := by linarith
  have hP3 : (8:ℝ) ≤ P^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sq_nonneg P)]
  have heq : P^(2*C+3) = (P^C)^2 * P^3 := by
    rw [Real.rpow_add hPpos,show 2*C=C*2 by ring,
      Real.rpow_mul hPpos.le,Real.rpow_two]
    exact congrArg (fun x : ℝ => (P^C)^2 * x) (Real.rpow_natCast P 3)
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right hP3 (sq_nonneg (P^C)),sq_nonneg (P^C-1)]

/-- Complete original f-box coordinate stage, including bounded comparisons.
All rates and gauge derivatives come from the original path. H>=1 and the
first derivative envelope are source preparation hypotheses. The source
corrected-delta smallness and alpha/zeta lower bound are not used. -/
theorem actual_original_f_box_stage
    (g vel : ℝ → Fin 6 → ℝ) (tau eta dtau deta : ℝ → ℝ)
    (S : Set ℝ) (t0 H P C : ℝ)
    (hS : Convex ℝ S) (ht0 : t0 ∈ S) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (hspan : ∀ t ∈ S, |t-t0| ≤ H)
    (hg : ∀ t ∈ S, HasDerivAt g (vel t) t)
    (htauDeriv : ∀ t ∈ S, HasDerivAt tau (dtau t) t)
    (hetaDeriv : ∀ t ∈ S, HasDerivAt eta (deta t) t)
    (htau : ∀ t ∈ S, tau t = originalAffineBodyCoordinates (g t) (vel t) 2)
    (heta : ∀ t ∈ S, eta t = originalAffineBodyCoordinates (g t) (vel t) 4)
    (hF : ∀ t ∈ S, originalAffineBodyCoordinates (g t) (vel t) 5 = 1)
    (hbody : ∀ t ∈ S, ∀ i : Fin 6,
      |originalAffineBodyCoordinates (g t) (vel t) i| ≤ P^C)
    (hdtau : ∀ t ∈ S, |dtau t| ≤ P^C/H)
    (hdeta : ∀ t ∈ S, |deta t| ≤ P^C/H) :
    let u := rawU H S g vel deta
    let v := rawV H S g vel dtau
    0 ≤ u ∧ 0 ≤ v ∧ u ≤ P^(C+1)*H^2 ∧
      (∀ t ∈ S, BoxBound (originalUpperRelativeFrame (g t0) (g t))
        (P^(4*C+7)) H u) ∧
      (∀ t ∈ S, ∀ l r : Fin 6 → ℝ,
        (∀ i, |l i| ≤ P^C) → (∀ i, |r i| ≤ P^C) →
        BoxBound (originalUpperAffineComp
          (originalUpperAffineComp l (originalUpperRelativeFrame (g t0) (g t))) r)
          (P^(6*C+11)) H u) := by
  have hPpos : 0 < P := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hH0 := hHpos.le
  have hB1 : 1 ≤ P^C := by simpa [hF t0 ht0] using hbody t0 ht0 5
  have hB0 := zero_le_one.trans hB1
  have hdiv : P^C/H ≤ P^C := by
    apply (div_le_iff₀ hHpos).mpr
    exact le_mul_of_one_le_right hB0 hH
  have hdt (t : ℝ) (ht : t ∈ S) : |dtau t| ≤ P^C := (hdtau t ht).trans hdiv
  have hde (t : ℝ) (ht : t ∈ S) : |deta t| ≤ P^C := (hdeta t ht).trans hdiv
  let B := P^C
  let M := B^2+2*B
  have hM1 : 1 ≤ M := by dsimp [M,B]; nlinarith [sq_nonneg (P^C)]
  have hBM : B ≤ M := by dsimp [M]; nlinarith [sq_nonneg B]
  have hD (t : ℝ) (ht : t ∈ S) : |correctedDelta g vel deta t| ≤ 2*B := by
    calc
      _ ≤ |originalAffineBodyCoordinates (g t) (vel t) 3|+|deta t| := abs_add _ _
      _ ≤ B+B := add_le_add (hbody t ht 3) (hde t ht)
      _ = _ := by ring
  have hZ (t : ℝ) (ht : t ∈ S) : |correctedZeta g vel dtau t| ≤ M := by
    have hm : |originalAffineBodyCoordinates (g t) (vel t) 0 *
        originalAffineBodyCoordinates (g t) (vel t) 4| ≤ B^2 := by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hbody t ht 0) (hbody t ht 4) (abs_nonneg _) hB0
    calc
      _ ≤ |originalAffineBodyCoordinates (g t) (vel t) 1| +
          |originalAffineBodyCoordinates (g t) (vel t) 0 *
            originalAffineBodyCoordinates (g t) (vel t) 4| + |dtau t| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ B+B^2+B := add_le_add (add_le_add (hbody t ht 1) hm) (hdt t ht)
      _ = M := by dsimp [M]; ring
  obtain ⟨hD0,hDup,hDpoint⟩ := rateSup_bounds S (correctedDelta g vel deta) t0 (2*B) ht0 hD
  obtain ⟨hZ0,_,_⟩ := rateSup_bounds S (correctedZeta g vel dtau) t0 M ht0 hZ
  let u := rawU H S g vel deta
  have hu : 0 ≤ u := mul_nonneg (sq_nonneg H) hD0
  have hv : 0 ≤ rawV H S g vel dtau := mul_nonneg hH0 hZ0
  have huupper : u ≤ P^(C+1)*H^2 := by
    have h2B : 2*B ≤ P^(C+1) := by
      rw [Real.rpow_add hPpos,Real.rpow_one]
      dsimp [B]
      nlinarith only [mul_le_mul_of_nonneg_left hP hB0]
    have h := mul_le_mul_of_nonneg_left (hDup.trans h2B) (sq_nonneg H)
    simpa only [u,rawU,mul_comm] using h
  let q := gaugedRelativePath g tau eta t0
  have hq : ∀ t ∈ S, HasDerivAt q
      (originalUpperBodyVelocity (q t)
        ![originalAffineBodyCoordinates (g t) (vel t) 0,
          correctedZeta g vel dtau t,0,correctedDelta g vel deta t,0,1]) t := by
    intro t ht
    have hg' : HasDerivAt g
        (originalUpperBodyVelocity (g t) (originalAffineBodyCoordinates (g t) (vel t))) t := by
      simpa only [originalUpperBodyVelocity_body] using hg t ht
    have hgauge := gaugedPath_hasDerivAt g (originalAffineBodyCoordinates (g t) (vel t))
      tau eta t (dtau t) (deta t) hg' (htauDeriv t ht) (hetaDeriv t ht)
      (htau t ht) (heta t ht) (hF t ht)
    have hr := originalUpperRelativeFrame_hasDerivAt (gaugedPath g tau eta)
      (gaugedPath g tau eta t0)
      (gaugeBodyRates (originalAffineBodyCoordinates (g t) (vel t)) (dtau t) (deta t)) t hgauge
    simpa only [q,gaugedRelativePath,gaugeBodyRates,correctedZeta,correctedDelta] using hr
  have hzero : q t0 = 0 := originalUpperRelativeFrame_self _
  have hraw := FGaugeWidthCalculus.gauged_coordinate_bounds q
    (fun t => originalAffineBodyCoordinates (g t) (vel t) 0)
    (correctedZeta g vel dtau) (correctedDelta g vel deta) S t0 H
    (rateSup S (correctedDelta g vel deta)) M hS ht0 hH0 hspan hzero hq hD0
    (zero_le_one.trans hM1) (fun t ht => (hbody t ht 0).trans hBM) hZ hDpoint
  have hK0 : 1 ≤ 2*M := by linarith
  have hKpower : 2*M ≤ P^(2*C+3) := common_envelope_power P C hP hB1
  have hK1 : 1 ≤ P^(2*C+3) := hK0.trans hKpower
  have hKg (t : ℝ) (ht : t ∈ S) : BoxBound (q t) (P^(2*C+3)) H u := by
    apply boxBound_mono hH hu hKpower
    apply raw_bounds_to_box (q t) H u M hH hu hM1
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := hraw t ht
    have hcancel : H * rateSup S (correctedDelta g vel deta) = u/H := by
      dsimp [u,rawU]
      field_simp
      ring
    exact ⟨ha,hb,hc,hd.trans_eq hcancel,he,hf⟩
  have htbound (t : ℝ) (ht : t ∈ S) : |tau t| ≤ P^C := by rw [htau t ht]; exact hbody t ht 2
  have hebound (t : ℝ) (ht : t ∈ S) : |eta t| ≤ P^C := by rw [heta t ht]; exact hbody t ht 4
  have horiginal (t : ℝ) (ht : t ∈ S) :
      BoxBound (originalUpperRelativeFrame (g t0) (g t)) (P^(4*C+7)) H u := by
    have h := multiplyback_box_bound (q t) (P^(2*C+3)) (P^C) H u
      (tau t0) (tau t) (eta t0) (eta t) hH hu hK1 hB1 (hKg t ht)
      (htbound t0 ht0) (htbound t ht) (hebound t0 ht0) (hebound t ht)
    have hid : multiplyback (q t) (tau t0) (tau t) (eta t0) (eta t) =
        originalUpperRelativeFrame (g t0) (g t) :=
      gauged_relative_multiplyback (g t0) (g t) (tau t0) (tau t) (eta t0) (eta t)
    rw [hid] at h
    apply boxBound_mono hH hu _ h
    convert two_comparisons_power P C (2*C+3) hP using 1; ring
  have hKoriginal : 1 ≤ P^(4*C+7) := by
    have hpow := two_comparisons_power P C (2*C+3) hP
    have hB2 : 1 ≤ (P^C)^2 := by nlinarith [sq_nonneg (P^C-1)]
    have hprod : 1 ≤ P^(2*C+3)*(P^C)^2 := one_le_mul_of_one_le_of_one_le hK1 hB2
    have h1 : 1 ≤ 16*P^(2*C+3)*(P^C)^2 := by nlinarith
    convert h1.trans hpow using 1; ring
  refine ⟨hu,hv,huupper,horiginal,?_⟩
  intro t ht l r hl hr
  have h := boxBound_two_bounded (originalUpperRelativeFrame (g t0) (g t)) l r
    (P^(4*C+7)) (P^C) H u hH hu hKoriginal hB1 (horiginal t ht) hl hr
  apply boxBound_mono hH hu _ h
  convert two_comparisons_power P C (4*C+7) hP using 1; ring

end PaperI.OriginalFBoxStage
