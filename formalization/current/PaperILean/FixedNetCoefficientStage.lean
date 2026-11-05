import PaperILean.FiniteSampleEnvelope
import PaperILean.OriginalSamplingComparisons

/-! I1387-I1395: the full coefficient-volume implication for fixed additional
sample nets. All admissible actual tuples are retained, including phase-dependent
choices. A good complete minor is on an actual tuple or its comparison proxy,
not on a rounded reference. This does not construct the geometric common cover. -/

noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace PaperI.FixedNetCoefficientStage
open OriginalSamplingComparisons FiniteSampleEnvelope

abbrev NetChoice {r : ℕ} (nets : Fin r → Finset (Fin 6 → ℝ)) :=
  (i : Fin r) → nets i

def reference {r : ℕ} {nets : Fin r → Finset (Fin 6 → ℝ)}
    (q : NetChoice nets) : Fin (r + 1) → (Fin 6 → ℝ) :=
  Fin.cases 0 (fun i => (q i).val)

def sampleMinor (k m : ℕ) (h : Fin m → (Fin 6 → ℝ))
    (rows : MonomialIndex k → Fin m × MonomialIndex k) :
    CoefficientSpace k →ₗ[ℝ] CoefficientSpace k :=
  LinearMap.pi fun α => (LinearMap.proj (rows α)).comp (completeSampleMap k m h)

theorem sampleMinor_apply (k m : ℕ) (h : Fin m → (Fin 6 → ℝ))
    (rows : MonomialIndex k → Fin m × MonomialIndex k)
    (J : CoefficientSpace k) (α : MonomialIndex k) :
    sampleMinor k m h rows J α = completeSampleMap k m h J (rows α) := rfl

abbrev Certificate (k m : ℕ) :=
  (Fin m → (Fin 6 → ℝ)) × (Fin m → (Fin 6 → ℝ)) ×
    (MonomialIndex k → Fin m × MonomialIndex k)

namespace Certificate

def actual {k m : ℕ} (w : Certificate k m) : Fin m → (Fin 6 → ℝ) := w.1

def proxy {k m : ℕ} (w : Certificate k m) : Fin m → (Fin 6 → ℝ) := w.2.1

def rows {k m : ℕ} (w : Certificate k m) : MonomialIndex k → Fin m × MonomialIndex k :=
  w.2.2

end Certificate

def Eligible (k r : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
    (T Δ D : ℝ) (q : NetChoice nets) (w : Certificate k (r + 1)) : Prop :=
  RightClose T w.actual (reference q) ∧ Function.Injective w.rows ∧
    Δ ≤ |LinearMap.det (sampleMinor k (r + 1) w.proxy w.rows)| ∧
    ∀ G, coordinateL2Norm (completeSampleMap k (r + 1) w.proxy G) ≤
      D * coordinateL2Norm (completeSampleMap k (r + 1) w.actual G)

def fullEnvelope (k r : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
    (T Δ D W : ℝ) : Set (CoefficientSpace k) :=
  comparisonEnvelope (fun w : Certificate k (r + 1) =>
    completeSampleMap k (r + 1) w.actual) (Eligible k r nets T Δ D) W

theorem netChoice_card_le {r N : ℕ} (nets : Fin r → Finset (Fin 6 → ℝ))
    (hnets : ∀ i, (nets i).card ≤ N) : Fintype.card (NetChoice nets) ≤ N ^ r := by
  classical
  calc
    Fintype.card (NetChoice nets) = ∏ i, (nets i).card := by
      simp [NetChoice, Fintype.card_pi]
    _ ≤ ∏ _i : Fin r, N := Finset.prod_le_prod' (fun i _ => hnets i)
    _ = N ^ r := by simp

theorem fullEnvelope_volume_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r N : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
      (T Δ D W : ℝ), 0 ≤ T → 0 < Δ → 0 ≤ D → 0 ≤ W →
      (∀ i, (nets i).card ≤ N) →
      coefficientMeasure k (fullEnvelope k r nets T Δ D W) ≤
        (N : ℝ≥0∞) ^ r * ENNReal.ofReal
          (Δ⁻¹ * (2 * (D * (C * (3 * (1 + T)) ^ (2 * k)) *
            (C * (3 * (1 + T)) ^ (2 * k)) * W)) ^ Fintype.card (MonomialIndex k)) := by
  classical
  obtain ⟨C, hC, hComp⟩ := completeSampleMap_rightClose_bound k
  refine ⟨C, hC, ?_⟩
  intro r N nets T Δ D W hT hΔ hD hW hnets
  let B := C * (3 * (1 + T)) ^ (2 * k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv := finite_comparison_envelope_bound
    (fun w : Certificate k (r + 1) => completeSampleMap k (r + 1) w.actual)
    (fun q : NetChoice nets => completeSampleMap k (r + 1) (reference q))
    (fun w => sampleMinor k (r + 1) w.proxy w.rows)
    (Eligible k r nets T Δ D) Δ B D W hΔ hB hD hW
    (fun _ _ hw => hw.2.2.1)
    (fun q w hw G => (hComp (r + 1) T hT w.actual (reference q) hw.1 G).1)
    (fun q w hw G => (hComp (r + 1) T hT w.actual (reference q) hw.1 G).2)
    (fun _ w hw G α =>
      (SampleMinorVolume.abs_le_coordinateL2Norm
        (completeSampleMap k (r + 1) w.proxy G) (w.rows α)).trans (hw.2.2.2 G))
  have hc : (Fintype.card (NetChoice nets) : ℝ≥0∞) ≤ (N : ℝ≥0∞) ^ r := by
    exact_mod_cast netChoice_card_le nets hnets
  exact hv.trans (mul_le_mul_right' hc _)

theorem fullEnvelope_polynomial_bound (k r : ℕ) (Ct Cm Cw : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (P Δ : ℝ) (N : ℕ)
      (nets : Fin r → Finset (Fin 6 → ℝ)),
      2 ≤ P → 0 < Δ → (∀ i, (nets i).card ≤ N) →
      coefficientMeasure k (fullEnvelope k r nets (P ^ Ct) Δ (P ^ Cm) (P ^ Cw)) ≤
        ENNReal.ofReal (P ^ E * Δ⁻¹) * (N : ℝ≥0∞) ^ r := by
  obtain ⟨C, hC, hvolume⟩ := fullEnvelope_volume_bound k
  obtain ⟨E, hE, hpoly⟩ := SampleMinorVolume.polynomial_box_factor_le
    k (Fintype.card (MonomialIndex k)) C Ct Cm Cw hC
  refine ⟨E, hE, ?_⟩
  intro P Δ N nets hP hΔ hnets
  have hP0 : 0 ≤ P := by linarith
  have hv := hvolume r N nets (P ^ Ct) Δ (P ^ Cm) (P ^ Cw)
    (Real.rpow_nonneg hP0 _) hΔ (Real.rpow_nonneg hP0 _)
    (Real.rpow_nonneg hP0 _) hnets
  have hb : (2 * (P ^ Cm * (C * (3 * (1 + P ^ Ct)) ^ (2 * k)) *
      (C * (3 * (1 + P ^ Ct)) ^ (2 * k)) * P ^ Cw)) ^
        Fintype.card (MonomialIndex k) ≤ P ^ E := by
    convert hpoly P hP using 1; ring
  calc
    _ ≤ (N : ℝ≥0∞) ^ r * ENNReal.ofReal
        (Δ⁻¹ * (2 * (P ^ Cm * (C * (3 * (1 + P ^ Ct)) ^ (2 * k)) *
          (C * (3 * (1 + P ^ Ct)) ^ (2 * k)) * P ^ Cw)) ^
            Fintype.card (MonomialIndex k)) := hv
    _ ≤ (N : ℝ≥0∞) ^ r * ENNReal.ofReal (Δ⁻¹ * P ^ E) :=
      mul_le_mul_left' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hΔ.le))) _
    _ = _ := by rw [mul_comm (Δ⁻¹), mul_comm]

def directEnvelope (k r : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
    (T Δ W : ℝ) : Set (CoefficientSpace k) :=
  {J | ∃ (q : NetChoice nets) (h : Fin (r + 1) → (Fin 6 → ℝ))
    (rows : MonomialIndex k → Fin (r + 1) × MonomialIndex k),
    RightClose T h (reference q) ∧ Function.Injective rows ∧
      Δ ≤ |LinearMap.det (sampleMinor k (r + 1) h rows)| ∧
      coordinateL2Norm (completeSampleMap k (r + 1) h J) ≤ W}

theorem directEnvelope_subset_fullEnvelope (k r : ℕ)
    (nets : Fin r → Finset (Fin 6 → ℝ)) (T Δ W : ℝ) :
    directEnvelope k r nets T Δ W ⊆ fullEnvelope k r nets T Δ 1 W := by
  rintro J ⟨q, h, rows, hclose, hinj, hdet, hW⟩
  refine ⟨q, ⟨h, h, rows⟩, ⟨hclose, hinj, hdet, ?_⟩, hW⟩
  intro G
  simp [Certificate.actual, Certificate.proxy]

theorem directEnvelope_polynomial_bound (k r : ℕ) (Ct Cw : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (P Δ : ℝ) (N : ℕ)
      (nets : Fin r → Finset (Fin 6 → ℝ)),
      2 ≤ P → 0 < Δ → (∀ i, (nets i).card ≤ N) →
      coefficientMeasure k (directEnvelope k r nets (P ^ Ct) Δ (P ^ Cw)) ≤
        ENNReal.ofReal (P ^ E * Δ⁻¹) * (N : ℝ≥0∞) ^ r := by
  obtain ⟨E, hE, hvolume⟩ := fullEnvelope_polynomial_bound k r Ct 0 Cw
  refine ⟨E, hE, ?_⟩
  intro P Δ N nets hP hΔ hnets
  have hv := hvolume P Δ N nets hP hΔ hnets
  rw [Real.rpow_zero] at hv
  exact (measure_mono (directEnvelope_subset_fullEnvelope k r nets _ _ _)).trans hv

theorem norm_le_of_squared_comparison (P Cm a b : ℝ) (hP : 2 ≤ P)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : P ^ (-Cm) * a ^ 2 ≤ b ^ 2) :
    a ≤ P ^ (max Cm 0) * b := by
  have hPpos : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hprod : P ^ Cm * P ^ (-Cm) = 1 := by
    rw [← Real.rpow_add hPpos, add_neg_cancel, Real.rpow_zero]
  have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hPpos.le Cm)
  have hs : a ^ 2 ≤ P ^ Cm * b ^ 2 := by
    calc
      a ^ 2 = (P ^ Cm * P ^ (-Cm)) * a ^ 2 := by rw [hprod, one_mul]
      _ = P ^ Cm * (P ^ (-Cm) * a ^ 2) := by ring
      _ ≤ P ^ Cm * b ^ 2 := hmul
  have hpower : P ^ Cm ≤ (P ^ (max Cm 0)) ^ 2 := by
    calc
      P ^ Cm ≤ P ^ (max Cm 0 + max Cm 0) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by
          have h1 := le_max_left Cm 0
          have h2 := le_max_right Cm 0
          linarith)
      _ = (P ^ (max Cm 0)) ^ 2 := by rw [Real.rpow_add hPpos]; ring
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hpower (sq_nonneg b))
  have hn := mul_nonneg (Real.rpow_nonneg hPpos.le (max Cm 0)) hb
  nlinarith

def SquaredEligible (k r : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
    (T Δ P Cm : ℝ) (q : NetChoice nets) (w : Certificate k (r + 1)) : Prop :=
  RightClose T w.actual (reference q) ∧ Function.Injective w.rows ∧
    Δ ≤ |LinearMap.det (sampleMinor k (r + 1) w.proxy w.rows)| ∧
    ∀ G, P ^ (-Cm) * coordinateL2Norm (completeSampleMap k (r + 1) w.proxy G) ^ 2 ≤
      coordinateL2Norm (completeSampleMap k (r + 1) w.actual G) ^ 2 ∧
      coordinateL2Norm (completeSampleMap k (r + 1) w.actual G) ^ 2 ≤
        P ^ Cm * coordinateL2Norm (completeSampleMap k (r + 1) w.proxy G) ^ 2

def squaredEnvelope (k r : ℕ) (nets : Fin r → Finset (Fin 6 → ℝ))
    (T Δ P Cm W : ℝ) : Set (CoefficientSpace k) :=
  comparisonEnvelope (fun w : Certificate k (r + 1) =>
    completeSampleMap k (r + 1) w.actual) (SquaredEligible k r nets T Δ P Cm) W

theorem squaredEnvelope_subset_fullEnvelope (k r : ℕ)
    (nets : Fin r → Finset (Fin 6 → ℝ)) (T Δ P Cm W : ℝ) (hP : 2 ≤ P) :
    squaredEnvelope k r nets T Δ P Cm W ⊆
      fullEnvelope k r nets T Δ (P ^ (max Cm 0)) W := by
  rintro J ⟨q, w, hw, hW⟩
  refine ⟨q, w, ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩, hW⟩
  intro G
  exact norm_le_of_squared_comparison P Cm _ _ hP
    (coordinateL2Norm_nonneg _) (coordinateL2Norm_nonneg _) (hw.2.2.2 G).1

theorem squaredEnvelope_polynomial_bound (k r : ℕ) (Ct Cm Cw : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (P Δ : ℝ) (N : ℕ)
      (nets : Fin r → Finset (Fin 6 → ℝ)),
      2 ≤ P → 0 < Δ → (∀ i, (nets i).card ≤ N) →
      coefficientMeasure k
        (squaredEnvelope k r nets (P ^ Ct) Δ P Cm (P ^ Cw)) ≤
        ENNReal.ofReal (P ^ E * Δ⁻¹) * (N : ℝ≥0∞) ^ r := by
  obtain ⟨E, hE, hvolume⟩ := fullEnvelope_polynomial_bound k r Ct (max Cm 0) Cw
  refine ⟨E, hE, ?_⟩
  intro P Δ N nets hP hΔ hnets
  exact (measure_mono
    (squaredEnvelope_subset_fullEnvelope k r nets _ _ _ _ _ hP)).trans
      (hvolume P Δ N nets hP hΔ hnets)

end PaperI.FixedNetCoefficientStage
