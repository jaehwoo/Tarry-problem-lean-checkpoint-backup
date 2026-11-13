import PaperILean.PreparedBufferedPlanarArc
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! I1263: Euclidean area of the actual closed transverse strip. Signed
coordinates are the original fixed coordinate choices, not new geometric
witnesses. Continuity is required only on the supplied closed interval. -/

noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped ENNReal

def signedPlanarCoordinates (i : Fin 2) (σ : ℝ)
    (p : WithLp 2 (Fin 2 → ℝ)) : ℝ × ℝ :=
  let v := (WithLp.equiv 2 (Fin 2 → ℝ)) p
  if i=0 then (σ*v 0,v 1) else (σ*v 1,v 0)

theorem signedPlanarCoordinates_stripPoint (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (q u : ℝ) :
    signedPlanarCoordinates i σ (signedPlanarStripPoint i σ h q u) = (q,h q+u) := by
  fin_cases i <;> rcases hσ with rfl | rfl <;>
    simp [signedPlanarCoordinates,signedPlanarStripPoint,signedPlanarDecode]

theorem signedPlanarCoordinates_injective (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) : Function.Injective (signedPlanarCoordinates i σ) := by
  intro p q hp
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext j
  fin_cases i <;> fin_cases j <;> rcases hσ with rfl | rfl <;>
    simp_all [signedPlanarCoordinates]

theorem signedPlanarCoordinates_measurePreserving (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) : MeasurePreserving (signedPlanarCoordinates i σ) := by
  have hsign : MeasurePreserving (fun x : ℝ => σ*x) volume volume := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using (MeasurePreserving.id (volume : Measure ℝ))
    · simpa only [neg_one_mul] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpair := (volume_preserving_finTwoArrow ℝ).comp
    (PiLp.volume_preserving_equiv (Fin 2))
  have hprod := hsign.prod (MeasurePreserving.id (volume : Measure ℝ))
  fin_cases i
  · convert hprod.comp hpair using 1
  · convert hprod.comp (Measure.measurePreserving_swap.comp hpair) using 1

theorem mem_signedPlanarStrip_iff_coordinates (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (J : Set ℝ) (w : ℝ)
    (p : WithLp 2 (Fin 2 → ℝ)) :
    p ∈ signedPlanarStrip i σ h J w ↔
      (signedPlanarCoordinates i σ p).1 ∈ J ∧
      |(signedPlanarCoordinates i σ p).2-h (signedPlanarCoordinates i σ p).1| ≤ w := by
  constructor
  · rintro ⟨q,hq,u,hu,rfl⟩
    simpa [signedPlanarCoordinates_stripPoint i σ hσ] using And.intro hq hu
  · rintro ⟨hq,hu⟩
    refine ⟨(signedPlanarCoordinates i σ p).1,hq,
      (signedPlanarCoordinates i σ p).2-h (signedPlanarCoordinates i σ p).1,hu,?_⟩
    apply signedPlanarCoordinates_injective i σ hσ
    rw [signedPlanarCoordinates_stripPoint i σ hσ]
    simp

theorem volume_closed_vertical_strip (g : ℝ → ℝ) (hg : Measurable g)
    (a b w : ℝ) :
    volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ |p.2-g p.1| ≤ w} =
      ENNReal.ofReal (b-a)*ENNReal.ofReal (2*w) := by
  have heq : {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ |p.2-g p.1| ≤ w} =
      {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (g p.1-w) (g p.1+w)} := by
    ext p
    simp only [mem_setOf_eq,mem_Icc,abs_le]
    constructor <;> rintro ⟨hp,h₁,h₂⟩ <;> exact ⟨hp,by linarith,by linarith⟩
  rw [heq]
  change (volume.prod volume) _ = _
  rw [Measure.prod_apply (measurableSet_region_between_cc
    (hg.sub measurable_const) (hg.add measurable_const) measurableSet_Icc)]
  have hsection : (fun x : ℝ => volume {y : ℝ | x ∈ Icc a b ∧ y ∈ Icc (g x-w) (g x+w)}) =
      (Icc a b).indicator (fun _ => ENNReal.ofReal (2*w)) := by
    funext x
    by_cases hx : x ∈ Icc a b
    · simp only [hx,true_and,indicator_of_mem,setOf_mem_eq,Real.volume_Icc]
      congr 1
      ring
    · simp [hx]
  change (∫⁻ x : ℝ, volume {y : ℝ | x ∈ Icc a b ∧ y ∈ Icc (g x-w) (g x+w)}) = _
  rw [hsection,lintegral_indicator measurableSet_Icc]
  simp [Real.volume_Icc,mul_comm]

/-- Closed boundaries are included. The formula also covers negative width,
empty/reversed intervals and singleton intervals through `ENNReal.ofReal`. -/
theorem signedPlanarStrip_measurable_volume (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (a b w : ℝ)
    (hh : ContinuousOn h (Icc a b)) :
    MeasurableSet (signedPlanarStrip i σ h (Icc a b) w) ∧
      volume (signedPlanarStrip i σ h (Icc a b) w) =
        ENNReal.ofReal (b-a)*ENNReal.ofReal (2*w) := by
  classical
  let g : ℝ → ℝ := (Icc a b).piecewise h (fun _ => 0)
  have hg : Measurable g := hh.measurable_piecewise continuousOn_const measurableSet_Icc
  let T : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ |p.2-g p.1| ≤ w}
  have hT : MeasurableSet T :=
    (measurable_fst measurableSet_Icc).inter
      (measurableSet_le (continuous_abs.measurable.comp
        (measurable_snd.sub (hg.comp measurable_fst))) measurable_const)
  have heq : signedPlanarStrip i σ h (Icc a b) w = signedPlanarCoordinates i σ ⁻¹' T := by
    ext p
    rw [mem_signedPlanarStrip_iff_coordinates i σ hσ]
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases hq : (signedPlanarCoordinates i σ p).1 ∈ Icc a b
    · simp [g,hq]
    · simp [hq]
  have hmp := signedPlanarCoordinates_measurePreserving i σ hσ
  refine ⟨heq ▸ hmp.measurable hT,?_⟩
  rw [heq,hmp.measure_preimage hT.nullMeasurableSet]
  exact volume_closed_vertical_strip g hg a b w

theorem volume_real_signedPlanarStrip (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (a b w : ℝ)
    (hh : ContinuousOn h (Icc a b)) (hab : a ≤ b) (hw : 0 ≤ w) :
    volume.real (signedPlanarStrip i σ h (Icc a b) w) = (b-a)*(2*w) := by
  change (volume (signedPlanarStrip i σ h (Icc a b) w)).toReal = _
  rw [(signedPlanarStrip_measurable_volume i σ hσ h a b w hh).2,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hw)]

theorem volume_real_signedPlanarStrip_quarter (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (a b W : ℝ)
    (hh : ContinuousOn h (Icc a b)) (hab : a ≤ b) (hW : 0 ≤ W) :
    volume.real (signedPlanarStrip i σ h (Icc a b) (W/4)) = (b-a)*W/2 := by
  rw [volume_real_signedPlanarStrip i σ hσ h a b (W/4) hh hab (by positivity)]
  ring

theorem signedPlanarStrip_area_lower_bound (i : Fin 2) (σ : ℝ)
    (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ) (u v W R Cspan : ℝ) (Kprep : ℕ)
    (hh : ContinuousOn h (Icc u v)) (huv : u ≤ v) (hW : 0 ≤ W)
    (hC : 0 < Cspan) (hK : 0 < Kprep)
    (hspan : R ≤ Cspan*(Kprep : ℝ)*(v-u)) :
    R*W/(2*Cspan*(Kprep : ℝ)) ≤
      volume.real (signedPlanarStrip i σ h (Icc u v) (W/4)) := by
  rw [volume_real_signedPlanarStrip_quarter i σ hσ h u v W hh huv hW]
  have hKr : 0 < (Kprep : ℝ) := by exact_mod_cast hK
  apply (div_le_iff₀ (by positivity : 0 < 2*Cspan*(Kprep : ℝ))).mpr
  have hm := mul_le_mul_of_nonneg_right hspan hW
  nlinarith

end PaperI
