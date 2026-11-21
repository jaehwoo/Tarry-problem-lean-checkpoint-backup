import Revision.CapInterval
import PaperILean.CommonNullEndpointReadout

open Set MeasureTheory
open scoped ENNReal
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic ParabolicCollar CommonNullAssignment ShortProjectionCaps
open PaperII.EndpointRangesWhole

/-- Fubini is performed using the area of the original physical collar. -/
theorem comparable_good {γ γ₀ : ℝ → Plane} {d v : Plane → ℝ} {E : Set Plane} {keep : Plane → Prop}
    {a₀ b₀ a b w : ℝ} {sf df n : ℕ}
    (Q : TransverseCollarGeometry γ γ₀ d v E keep a b a₀ b₀ w sf df n)
    (hab : a≤b) {G : Set Plane}
    (hG : ENNReal.ofReal ((b-a)*w) ≤ (2*(n:ℝ≥0∞))*volume G) :
    volume (collarImage γ d v a b w) ≤ (6*(n:ℝ≥0∞))*volume G := by
  obtain ⟨hm,_,_,hUpper⟩ := flux_rectangle_image_area _ a b w hab Q.differential
    Q.derivative (fun x hx => ⟨Q.det_lower x hx,Q.det_upper x hx⟩) n Q.multiplicity
  let pl : Coordinates ≃ᵐ Plane := MeasurableEquiv.finTwoArrow
  let S := collarMap γ d v '' fluxRectangle a b w
  have hImage : collarImage γ d v a b w = pl '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨_,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx,rfl⟩
  have hMeas : MeasurableSet (pl '' S) := pl.measurableEmbedding.measurableSet_image.mpr hm
  have hVol := (volume_preserving_finTwoArrow ℝ).measure_preimage hMeas.nullMeasurableSet
  change volume (pl ⁻¹' (pl '' S)) = volume (pl '' S) at hVol
  rw [preimage_image_eq _ pl.injective] at hVol
  rw [hImage,←hVol]
  calc
    volume S ≤ ENNReal.ofReal (3*w*(b-a)) := hUpper
    _ = 3 * ENNReal.ofReal ((b-a)*w) := by
      rw [show 3*w*(b-a)=3*((b-a)*w) by ring, ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
      norm_num
    _ ≤ 3*((2*(n:ℝ≥0∞))*volume G) := mul_le_mul_left' hG _
    _ = _ := by ring

/-- Enlarging the denominator from the prepared good image to any fixed
positive fraction of the full collar costs precisely the reciprocal fraction. -/
theorem positive_fraction_endpoint {ι : Type} [DecidableEq ι] {k : ℕ}
    {F : CoefficientSpace k} {P Λ δ U B θ : ℝ} {N e es rate sf df : ℕ}
    {E : Set Plane} {c d v : Plane → ℝ} {retain : Plane → Prop}
    {labels : Finset ι} {rep : ι → Plane} {fixed : ι → Fin 6 → ℝ}
    {route : CertificateRoute} {tag : ℝ × ℝ}
    (R : OriginalParabolicBandResult F P Λ δ U B N e es rate sf df E c d v retain labels rep fixed route tag)
    (hP : 2≤P) (hFin : volume E≠⊤) {S : Set Plane} (hθ : 0<θ)
    (hFraction : θ*volume.real R.patch.region ≤ volume.real S) :
    (∀ i∈labels, fixedEndpointProjection (fixed i) c d '' R.patch.region ⊆ parabolicEndpointCandidate P e R.scale.L) ∧
    volume.real (parabolicEndpointCandidate P e R.scale.L)/volume.real S ≤ P^(3*e+2)*R.scale.L^2/θ ∧
    volume.real (Icc (-(P^e*R.scale.L)) (P^e*R.scale.L)) ≤ P^(e+1)*R.scale.L := by
  let G := R.certificate.certificate.prepared.goodPhysical
  obtain ⟨hIn,hFactor,hShear⟩ := original_parabolic_endpoint_factor R hP
  have hReg : R.patch.region⊆E := R.certificate.patch_eq ▸ R.certificate.certificate.prepared.inside
  have hSub : G⊆R.patch.region := R.certificate.patch_eq ▸ R.certificate.certificate.prepared.goodPhysical_subset
  have hG : 0<volume.real G := lt_of_lt_of_le (mul_pos (inv_pos.mpr (pow_pos (by linarith) _))
    (zero_lt_one.trans_le R.scale.S_one)) R.certificate.certificate.prepared.area
  have hGS : θ*volume.real G≤volume.real S := (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (ne_top_of_le_ne_top hFin (measure_mono hReg)) (measure_mono hSub)) hθ.le).trans hFraction
  have hS := (mul_pos hθ hG).trans_le hGS
  have h := (div_le_iff₀ hG).mp hFactor
  refine ⟨hIn,(div_le_iff₀ hS).mpr ?_,hShear⟩
  have hK : 0≤P^(3*e+2)*R.scale.L^2 := mul_nonneg (pow_nonneg (by linarith) _) (sq_nonneg _)
  calc
    _ ≤ (P^(3*e+2)*R.scale.L^2)*volume.real G := h
    _ = (P^(3*e+2)*R.scale.L^2/θ)*(θ*volume.real G) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hGS (div_nonneg hK hθ.le)

end PaperI.CollarRevision
