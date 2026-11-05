import PaperILean.AnchoredMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Measurable majorants for the actual dyadic coefficient bins. No measurability
of the bins, disjointness of their measurable hulls, or actual rate integrand is
assumed. This is infrastructure for the whole weighted incidence proposition. -/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperI.PortfolioHolderEnvelope

open PaperI.AnchoredMoment

universe u

def binWeight (a q : ℝ) (i : BinIndex) : ℝ :=
  ((2 : ℝ) ^ i.1) ^ (-a) * ((2 : ℝ) ^ i.2.1) ^ q

theorem binWeight_nonneg (a q : ℝ) (i : BinIndex) : 0 ≤ binWeight a q i := by
  unfold binWeight
  positivity

def hullTerm {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : BinIndex → Set Ω) (a q : ℝ) (i : BinIndex) : Ω → ℝ≥0∞ :=
  (toMeasurable μ (E i)).indicator (fun _ => ENNReal.ofReal (binWeight a q i))

def hullEnvelope {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : BinIndex → Set Ω) (a q : ℝ) (x : Ω) : ℝ≥0∞ :=
  ∑' i : BinIndex, hullTerm μ E a q i x

theorem measurable_hullTerm {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : BinIndex → Set Ω) (a q : ℝ) (i : BinIndex) :
    Measurable (hullTerm μ E a q i) :=
  measurable_const.indicator (measurableSet_toMeasurable μ (E i))

theorem measurable_hullEnvelope {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : BinIndex → Set Ω) (a q : ℝ) : Measurable (hullEnvelope μ E a q) := by
  apply Measurable.ennreal_tsum
  exact fun i => measurable_hullTerm μ E a q i

theorem le_hullEnvelope {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : BinIndex → Set Ω) (a q : ℝ) (i : BinIndex) (x : Ω) (hx : x ∈ E i) :
    ENNReal.ofReal (binWeight a q i) ≤ hullEnvelope μ E a q x := by
  have hm : x ∈ toMeasurable μ (E i) := subset_toMeasurable μ (E i) hx
  calc
    _ = hullTerm μ E a q i x := by simp only [hullTerm, Set.indicator_of_mem hm]
    _ ≤ _ := ENNReal.le_tsum i

theorem weighted_volume_factor (P amplitude a q b τ c : ℝ) (i : BinIndex) :
    binWeight a q i * (P ^ c * amplitude * (2 : ℝ) ^ i.1 *
      ((2 : ℝ) ^ i.2.1) ^ (-b) * ((2 : ℝ) ^ i.2.2) ^ (-τ)) =
      P ^ c * amplitude * rawSeriesTerm a q b τ i := by
  have hn : ((2 : ℝ) ^ i.1) ^ (-a) * (2 : ℝ) ^ i.1 =
      ((2 : ℝ) ^ i.1) ^ (1 - a) := by
    conv_lhs => arg 2; rw [← Real.rpow_one ((2 : ℝ) ^ i.1)]
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hs : ((2 : ℝ) ^ i.2.1) ^ q * ((2 : ℝ) ^ i.2.1) ^ (-b) =
      ((2 : ℝ) ^ i.2.1) ^ (q - b) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
  unfold binWeight rawSeriesTerm
  calc
    _ = P ^ c * amplitude *
        (((2 : ℝ) ^ i.1) ^ (-a) * (2 : ℝ) ^ i.1) *
        (((2 : ℝ) ^ i.2.1) ^ q * ((2 : ℝ) ^ i.2.1) ^ (-b)) *
        ((2 : ℝ) ^ i.2.2) ^ (-τ) := by ring
    _ = _ := by rw [hn, hs]; ring

theorem hullEnvelope_lintegral_le_series {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : BinIndex → Set Ω) (P amplitude a q b τ c : ℝ)
    (hP : 0 ≤ P) (hA : 0 ≤ amplitude)
    (hzero : ∀ i, ¬ admissibleBin P c i → E i = ∅)
    (hvol : ∀ i, admissibleBin P c i → μ (E i) ≤
      ENNReal.ofReal (P ^ c * amplitude * (2 : ℝ) ^ i.1 *
        ((2 : ℝ) ^ i.2.1) ^ (-b) * ((2 : ℝ) ^ i.2.2) ^ (-τ))) :
    (∫⁻ x, hullEnvelope μ E a q x ∂μ) ≤
      ENNReal.ofReal (P ^ c * amplitude) *
        ∑' i : BinIndex, ENNReal.ofReal (literalDyadicSeriesTerm P a q b τ c i) := by
  classical
  have hfac : 0 ≤ P ^ c * amplitude := mul_nonneg (Real.rpow_nonneg hP _) hA
  have hterm (i : BinIndex) :
      (∫⁻ x, hullTerm μ E a q i x ∂μ) ≤
        ENNReal.ofReal (P ^ c * amplitude) *
          ENNReal.ofReal (literalDyadicSeriesTerm P a q b τ c i) := by
    rw [hullTerm, lintegral_indicator_const (measurableSet_toMeasurable μ (E i)),
      measure_toMeasurable]
    by_cases hi : admissibleBin P c i
    · have hv := mul_le_mul_left' (hvol i hi) (ENNReal.ofReal (binWeight a q i))
      rw [← ENNReal.ofReal_mul (binWeight_nonneg a q i), weighted_volume_factor] at hv
      simpa only [literalDyadicSeriesTerm, if_pos hi, ENNReal.ofReal_mul hfac] using hv
    · rw [hzero i hi]
      simp [literalDyadicSeriesTerm, hi]
  calc
    _ = ∑' i : BinIndex, ∫⁻ x, hullTerm μ E a q i x ∂μ := by
      apply lintegral_tsum
      exact fun i => (measurable_hullTerm μ E a q i).aemeasurable
    _ ≤ ∑' i : BinIndex, ENNReal.ofReal (P ^ c * amplitude) *
        ENNReal.ofReal (literalDyadicSeriesTerm P a q b τ c i) :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := ENNReal.tsum_mul_left

/-- Uniform majorant estimate, with the constant preceding the measure space,
all actual bins, and every nonnegative amplitude. -/
theorem hullEnvelope_uniform_bound (a q b τ c : ℝ)
    (ha : a < 1) (hb : q < b) (hτ : 0 < τ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
      (P amplitude : ℝ) (E : BinIndex → Set Ω),
      2 ≤ P → 0 ≤ amplitude →
      (∀ i, ¬ admissibleBin P c i → E i = ∅) →
      (∀ i, admissibleBin P c i → μ (E i) ≤
        ENNReal.ofReal (P ^ c * amplitude * (2 : ℝ) ^ i.1 *
          ((2 : ℝ) ^ i.2.1) ^ (-b) * ((2 : ℝ) ^ i.2.2) ^ (-τ))) →
      (∫⁻ x, hullEnvelope μ E a q x ∂μ) ≤
        ENNReal.ofReal (C * amplitude * P ^ (c * (2 - a))) := by
  obtain ⟨C, hC, hseries⟩ := literal_dyadic_series_ennreal_bound a q b τ c ha hb hτ hc
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ P amplitude E hP hA hzero hvol
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hfac : 0 ≤ P ^ c * amplitude := mul_nonneg (Real.rpow_nonneg hPpos.le _) hA
  calc
    _ ≤ ENNReal.ofReal (P ^ c * amplitude) *
        ∑' i : BinIndex, ENNReal.ofReal (literalDyadicSeriesTerm P a q b τ c i) :=
      hullEnvelope_lintegral_le_series μ E P amplitude a q b τ c hPpos.le hA hzero hvol
    _ ≤ ENNReal.ofReal (P ^ c * amplitude) *
        ENNReal.ofReal (C * P ^ (c * (1 - a))) :=
      mul_le_mul_left' (hseries P hP) _
    _ = ENNReal.ofReal (C * amplitude * P ^ (c * (2 - a))) := by
      rw [← ENNReal.ofReal_mul hfac]
      congr 1
      calc
        _ = C * amplitude * (P ^ c * P ^ (c * (1 - a))) := by ring
        _ = C * amplitude * P ^ (c + c * (1 - a)) := by rw [Real.rpow_add hPpos]
        _ = _ := by ring_nf

end PaperI.PortfolioHolderEnvelope
