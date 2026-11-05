import PaperILean.PortfolioHolderEnvelope
import PaperILean.RateWeightedHolder
import PaperILean.CoefficientChange
import PaperILean.GeneralAffineCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Whole Introduction I3079-I3118. The measurable assignment is kept fixed for
every original label. Dyadic bins are not assumed measurable: their measurable
hulls supply an integrable majorant before the fixed-frame change of variables. -/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperI.PortfolioHolder

open PaperI.AnchoredMoment PaperI.PortfolioHolderEnvelope

universe u v

/-- The original common assignment, with a fixed set of possible piece labels.
Only the pieces actually present at a phase carry dyadic data. -/
structure CommonRateAssignment (k : ℕ) (I : Type u) (J : Type v) where
  pieces : CoefficientSpace k → Set I
  assignment : (F : CoefficientSpace k) → J → Option (pieces F)
  rate : (F : CoefficientSpace k) → pieces F → ℤ
  scale : (F : CoefficientSpace k) → pieces F → ℕ
  aspect : (F : CoefficientSpace k) → pieces F → ℕ
  measurable_fibre : ∀ (j : J) (i : I), MeasurableSet
    {F | (assignment F j).map Subtype.val = some i}

/-- The two printed counts and the original rate/aspect restrictions. The
finite-fibre fields prevent replacing a finite count by ncard of an infinite set. -/
structure AssignmentBounds {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (P M C0 Λ Cstar : ℝ) (m : ℕ) : Prop where
  admissible : ∀ F i, (2 : ℝ) ^ D.rate F i ≤ P ^ Cstar ∧ D.aspect F i ≤ D.scale F i
  piece_finite : ∀ F (n : ℤ) (s t : ℕ),
    Set.Finite {i : D.pieces F | D.rate F i = n ∧ D.scale F i = s ∧ D.aspect F i = t}
  piece_count : ∀ F (n : ℤ) (s t : ℕ),
    (({i : D.pieces F | D.rate F i = n ∧ D.scale F i = s ∧ D.aspect F i = t} :
      Set (D.pieces F)).ncard : ℝ) ≤ M * PaperI.WeightedInverseSum.majorant m n s
  label_finite : ∀ F i, Set.Finite {j : J | D.assignment F j = some i}
  label_count : ∀ F i,
    (({j : J | D.assignment F j = some i} : Set J).ncard : ℝ) ≤
      C0 * Λ * ((2 : ℝ) ^ D.scale F i)

def assignedBin {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (F : CoefficientSpace k) (j : J) : Option BinIndex :=
  (D.assignment F j).map (fun i => (D.rate F i, D.scale F i, D.aspect F i))

def sourceBin {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (j : J) (d : BinIndex) : Set (CoefficientSpace k) :=
  {F | assignedBin D F j = some d}

def normalizedBin {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (centers : J → PhysicalSpace)
    (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (hdet : ∀ j, (matrices j).det ≠ 0)
    (j : J) (d : BinIndex) : Set (CoefficientSpace k) :=
  (affineCoefficientEquiv k (centers j) (matrices j) (hdet j)) '' sourceBin D j d

def frameVolume {J : Type v} (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (j : J) : ℝ :=
  |(matrices j).det|

def incidenceMass {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (coeff volume : J → ℝ) (F : CoefficientSpace k) : ℝ≥0∞ :=
  ∑' j, PaperI.RateWeightedHolderCore.activeCost (D.assignment F)
    (fun j => coeff j * volume j) j

theorem mem_sourceBin_iff {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (j : J) (d : BinIndex) (F : CoefficientSpace k) :
    F ∈ sourceBin D j d ↔ ∃ i : D.pieces F,
      D.assignment F j = some i ∧ (D.rate F i, D.scale F i, D.aspect F i) = d := by
  cases h : D.assignment F j with
  | none => simp [sourceBin, assignedBin, h]
  | some i => simp [sourceBin, assignedBin, h]

theorem sourceBin_empty_of_invalid {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (P Cstar : ℝ)
    (hparam : ∀ F i, (2 : ℝ) ^ D.rate F i ≤ P ^ Cstar ∧ D.aspect F i ≤ D.scale F i)
    (j : J) (d : BinIndex) (hd : ¬ admissibleBin P Cstar d) :
    sourceBin D j d = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro F hF
  obtain ⟨i, _, hi⟩ := (mem_sourceBin_iff D j d F).mp hF
  apply hd
  rw [← hi]
  exact hparam F i

theorem measurable_activeCost {k : ℕ} {I : Type u} {J : Type v} [Countable I]
    (D : CommonRateAssignment k I J) (c : J → ℝ) (j : J) :
    Measurable (fun F => PaperI.RateWeightedHolderCore.activeCost (D.assignment F) c j) := by
  classical
  have heq : {F | D.assignment F j ≠ none} =
      ⋃ i : I, {F | (D.assignment F j).map Subtype.val = some i} := by
    ext F
    cases h : D.assignment F j with
    | none => simp [h]
    | some i => simp [h]
  have hm : MeasurableSet {F | D.assignment F j ≠ none} := by
    rw [heq]
    exact MeasurableSet.iUnion (fun i => D.measurable_fibre j i)
  convert (measurable_const.indicator hm :
    Measurable ({F | D.assignment F j ≠ none}.indicator (fun _ => ENNReal.ofReal (c j)))) using 1
  funext F
  cases h : D.assignment F j <;> simp [PaperI.RateWeightedHolderCore.activeCost, h]

theorem measurable_incidenceMass {k : ℕ} {I : Type u} {J : Type v}
    [Countable I] [Countable J] (D : CommonRateAssignment k I J) (coeff volume : J → ℝ) :
    Measurable (incidenceMass D coeff volume) := by
  apply Measurable.ennreal_tsum
  exact fun j => measurable_activeCost D (fun j => coeff j * volume j) j

def normalizedEnvelope {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (centers : J → PhysicalSpace)
    (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (hdet : ∀ j, (matrices j).det ≠ 0)
    (a q : ℝ) (j : J) : CoefficientSpace k → ℝ≥0∞ :=
  hullEnvelope (coefficientMeasure k) (normalizedBin D centers matrices hdet j) a q

theorem measurable_normalizedEnvelope {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (centers : J → PhysicalSpace)
    (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (hdet : ∀ j, (matrices j).det ≠ 0)
    (a q : ℝ) (j : J) : Measurable (normalizedEnvelope D centers matrices hdet a q j) :=
  measurable_hullEnvelope _ _ _ _

theorem labelWeight_le_envelope {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (centers : J → PhysicalSpace)
    (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (hdet : ∀ j, (matrices j).det ≠ 0)
    (coeff : J → ℝ) (hb : ∀ j, 0 ≤ coeff j) (p a η : ℝ)
    (F : CoefficientSpace k) (j : J) :
    PaperI.RateWeightedHolder.labelWeight p a η (D.rate F) (D.scale F)
      (D.assignment F) coeff (frameVolume matrices) j ≤
      ENNReal.ofReal ((coeff j * frameVolume matrices j) ^ p) *
        normalizedEnvelope D centers matrices hdet a ((1 + η) * (p - 1)) j
          (affineCoefficientEquiv k (centers j) (matrices j) (hdet j) F) := by
  cases h : D.assignment F j with
  | none => simp only [PaperI.RateWeightedHolder.labelWeight, h]; exact zero_le _
  | some i =>
      let d : BinIndex := (D.rate F i, D.scale F i, D.aspect F i)
      have hm : affineCoefficientEquiv k (centers j) (matrices j) (hdet j) F ∈
          normalizedBin D centers matrices hdet j d :=
        ⟨F, (mem_sourceBin_iff D j d F).mpr ⟨i, h, rfl⟩, rfl⟩
      have henv := le_hullEnvelope (coefficientMeasure k)
        (normalizedBin D centers matrices hdet j) a ((1 + η) * (p - 1)) d _ hm
      have hw : 0 ≤ (coeff j * frameVolume matrices j) ^ p :=
        Real.rpow_nonneg (mul_nonneg (hb j) (abs_nonneg _)) _
      calc
        _ = ENNReal.ofReal ((coeff j * frameVolume matrices j) ^ p) *
            ENNReal.ofReal (binWeight a ((1 + η) * (p - 1)) d) := by
          simp only [PaperI.RateWeightedHolder.labelWeight, h, binWeight, d,
            ← ENNReal.ofReal_mul hw, mul_assoc]
        _ ≤ _ := mul_le_mul_left' henv _

theorem weighted_jacobian (b v p χ : ℝ) (hb : 0 ≤ b) (hv : 0 < v) :
    (b * v) ^ p * v ^ (-χ) = b ^ p * v ^ (p - χ) := by
  rw [Real.mul_rpow hb hv.le, mul_assoc, ← Real.rpow_add hv, sub_eq_add_neg]

theorem normalizedEnvelope_change {k : ℕ} {I : Type u} {J : Type v}
    (D : CommonRateAssignment k I J) (centers : J → PhysicalSpace)
    (matrices : J → Matrix (Fin 3) (Fin 3) ℝ) (hdet : ∀ j, (matrices j).det ≠ 0)
    (a q : ℝ) (j : J) :
    (∫⁻ F, normalizedEnvelope D centers matrices hdet a q j
      (affineCoefficientEquiv k (centers j) (matrices j) (hdet j) F) ∂coefficientMeasure k) =
      ENNReal.ofReal (frameVolume matrices j ^ (-(chi k : ℝ))) *
        ∫⁻ J, normalizedEnvelope D centers matrices hdet a q j J ∂coefficientMeasure k := by
  let e := affineCoefficientEquiv k (centers j) (matrices j) (hdet j)
  have he : Measurable e := e.toLinearMap.continuous_of_finiteDimensional.measurable
  have hm := (measurable_normalizedEnvelope D centers matrices hdet a q j).comp he
  have hc := lintegral_affineCoefficientChange_of_character k (centers j) (matrices j)
    (hdet j) (affineCoefficientMap_abs_det k (centers j) (matrices j))
    (fun F => normalizedEnvelope D centers matrices hdet a q j (e F)) hm
  simpa only [e, LinearEquiv.apply_symm_apply, frameVolume] using hc

/-- Whole weighted incidence proposition I3079-I3118, interpreted with the
nonnegative extended sum and integral for the original countable family.
All constants precede k, frames, assignments and original label weights. -/
theorem weighted_incidence_whole
    (p a η b τ Cstar : ℝ) (m : ℕ)
    (hp : 1 < p) (ha : 0 < a) (ha1 : a < 1) (hη : 0 < η)
    (hbexp : (1 + η) * (p - 1) < b) (hτ : 0 < τ) (hCstar : 0 < Cstar) :
    ∃ C : ℝ, 0 < C ∧ ∃ Aexp : ℝ, 0 ≤ Aexp ∧
      ∀ (k : ℕ) (I : Type u) (J : Type v) [Countable I] [Countable J]
        (P M C0 Λ amplitude : ℝ),
        2 ≤ P → 1 ≤ M → 1 ≤ C0 → 0 ≤ Λ → 0 ≤ amplitude →
      ∀ (D : CommonRateAssignment k I J)
        (centers : J → PhysicalSpace) (matrices : J → Matrix (Fin 3) (Fin 3) ℝ)
        (hdet : ∀ j, (matrices j).det ≠ 0) (coeff : J → ℝ),
        (∀ j, 0 ≤ coeff j) → AssignmentBounds D P M C0 Λ Cstar m →
        (∀ (j : J) (d : BinIndex), admissibleBin P Cstar d →
          coefficientMeasure k (normalizedBin D centers matrices hdet j d) ≤
            ENNReal.ofReal (P ^ Cstar * amplitude * (2 : ℝ) ^ d.1 *
              ((2 : ℝ) ^ d.2.1) ^ (-b) * ((2 : ℝ) ^ d.2.2) ^ (-τ))) →
        Measurable (fun F => incidenceMass D coeff (frameVolume matrices) F ^ p) ∧
        (∫⁻ F, incidenceMass D coeff (frameVolume matrices) F ^ p ∂coefficientMeasure k) ≤
          ENNReal.ofReal (C * P ^ Aexp * (C0 * M * Λ) ^ (p - 1) * amplitude) *
            ∑' j, ENNReal.ofReal (coeff j ^ p * frameVolume matrices j ^ (p - (chi k : ℝ))) := by
  obtain ⟨CH, hCH, AH, hAH, hpoint⟩ :=
    PaperI.RateWeightedHolder.rate_weighted_holder_stage p a η Cstar m hp ha ha1 hη hCstar
  obtain ⟨CS, hCS, hmoment⟩ :=
    hullEnvelope_uniform_bound a ((1 + η) * (p - 1)) b τ Cstar ha1 hbexp hτ hCstar
  refine ⟨CH * CS, mul_pos hCH hCS, AH + Cstar * (2 - a),
    add_nonneg hAH (mul_nonneg hCstar.le (by linarith)), ?_⟩
  intro k I J _ _ P M C0 Λ amplitude hP hM hC0 hΛ hA D centers matrices hdet coeff hb hD hvol
  let q : ℝ := (1 + η) * (p - 1)
  let v : J → ℝ := frameVolume matrices
  let e (j : J) := affineCoefficientEquiv k (centers j) (matrices j) (hdet j)
  let H (j : J) := normalizedEnvelope D centers matrices hdet a q j
  let cost (j : J) : ℝ≥0∞ := ENNReal.ofReal ((coeff j * v j) ^ p)
  let factor : ℝ := CH * P ^ AH * (C0 * M * Λ) ^ (p - 1)
  let moment : ℝ := CS * amplitude * P ^ (Cstar * (2 - a))
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hv (j : J) : 0 < v j := abs_pos.mpr (hdet j)
  have hH (j : J) : Measurable (H j) :=
    measurable_normalizedEnvelope D centers matrices hdet a q j
  have he (j : J) : Measurable (e j) :=
    (e j).toLinearMap.continuous_of_finiteDimensional.measurable
  have hcomp (j : J) : Measurable (fun F => H j (e j F)) := (hH j).comp (he j)
  have hsum : Measurable (fun F => ∑' j, cost j * H j (e j F)) :=
    Measurable.ennreal_tsum (fun j => measurable_const.mul (hcomp j))
  have hdom (F : CoefficientSpace k) :
      incidenceMass D coeff v F ^ p ≤
        ENNReal.ofReal factor * ∑' j, cost j * H j (e j F) := by
    have hh := hpoint P M C0 Λ hP hM hC0 hΛ (D.pieces F)
      (D.rate F) (D.scale F) (D.aspect F) (hD.admissible F) (hD.piece_finite F)
      (hD.piece_count F) J (D.assignment F) coeff v hb (fun j => (hv j).le)
      (hD.label_finite F) (hD.label_count F)
    exact hh.trans (mul_le_mul_left' (ENNReal.tsum_le_tsum
      (fun j => labelWeight_le_envelope D centers matrices hdet coeff hb p a η F j)) _)
  have hmom (j : J) : (∫⁻ x, H j x ∂coefficientMeasure k) ≤ ENNReal.ofReal moment := by
    apply hmoment (CoefficientSpace k) (coefficientMeasure k) P amplitude
      (normalizedBin D centers matrices hdet j) hP hA
    · intro d hd
      simp only [normalizedBin, sourceBin_empty_of_invalid D P Cstar hD.admissible j d hd,
        Set.image_empty]
    · exact hvol j
  have hterm (j : J) :
      cost j * (∫⁻ F, H j (e j F) ∂coefficientMeasure k) ≤
        ENNReal.ofReal moment *
          ENNReal.ofReal (coeff j ^ p * v j ^ (p - (chi k : ℝ))) := by
    have hjac := normalizedEnvelope_change D centers matrices hdet a q j
    change (∫⁻ F, H j (e j F) ∂coefficientMeasure k) =
      ENNReal.ofReal (v j ^ (-(chi k : ℝ))) *
        ∫⁻ x, H j x ∂coefficientMeasure k at hjac
    have hw : cost j * ENNReal.ofReal (v j ^ (-(chi k : ℝ))) =
        ENNReal.ofReal (coeff j ^ p * v j ^ (p - (chi k : ℝ))) := by
      rw [cost, ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (hb j) (hv j).le) _),
        weighted_jacobian (coeff j) (v j) p (chi k : ℝ) (hb j) (hv j)]
    calc
      _ = cost j * (ENNReal.ofReal (v j ^ (-(chi k : ℝ))) *
          ∫⁻ x, H j x ∂coefficientMeasure k) := by rw [hjac]
      _ ≤ cost j * (ENNReal.ofReal (v j ^ (-(chi k : ℝ))) * ENNReal.ofReal moment) :=
        mul_le_mul_left' (mul_le_mul_left' (hmom j) _) _
      _ = _ := by rw [← mul_assoc, hw, mul_comm]
  have hfactor0 : 0 ≤ factor := by
    dsimp [factor]
    exact mul_nonneg (mul_nonneg hCH.le (Real.rpow_nonneg hPpos.le _))
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one hC0)
        (le_trans zero_le_one hM)) hΛ) _)
  have hfactor : ENNReal.ofReal factor * ENNReal.ofReal moment =
      ENNReal.ofReal ((CH * CS) * P ^ (AH + Cstar * (2 - a)) *
        (C0 * M * Λ) ^ (p - 1) * amplitude) := by
    rw [← ENNReal.ofReal_mul hfactor0, Real.rpow_add hPpos]
    congr 1
    dsimp [factor, moment]
    ring
  refine ⟨ENNReal.continuous_rpow_const.measurable.comp (measurable_incidenceMass D coeff v), ?_⟩
  calc
    _ ≤ ∫⁻ F, ENNReal.ofReal factor * (∑' j, cost j * H j (e j F)) ∂coefficientMeasure k :=
      lintegral_mono hdom
    _ = ENNReal.ofReal factor *
        ∑' j, cost j * (∫⁻ F, H j (e j F) ∂coefficientMeasure k) := by
      rw [lintegral_const_mul _ hsum, lintegral_tsum
        (fun j => (measurable_const.mul (hcomp j)).aemeasurable)]
      congr 1
      apply tsum_congr
      intro j
      exact lintegral_const_mul (cost j) (hcomp j)
    _ ≤ ENNReal.ofReal factor * ∑' j, ENNReal.ofReal moment *
        ENNReal.ofReal (coeff j ^ p * v j ^ (p - (chi k : ℝ))) :=
      mul_le_mul_left' (ENNReal.tsum_le_tsum hterm) _
    _ = _ := by rw [ENNReal.tsum_mul_left, ← mul_assoc, hfactor]

end PaperI.PortfolioHolder
