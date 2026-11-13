import PaperILean.OriginalJointPreparedArcSelection
import PaperILean.SignedPlanarStripArea

/-! I1263: the SAME selected and prepared joint graph supplies a contained
strip and its actual Euclidean area. No endpoint frame change is involved. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

theorem OriginalJointPreparedArcData.strip_area_at
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → Fin 2 → ℝ}
    {H : ℕ} {n : Ω → ℕ} {t : Ω → ℕ → ℝ} {L : Ω → ℝ}
    {N K : ℕ} {C : ℝ}
    (D : OriginalJointPreparedArcData g H n t L N C K) (ω : Ω)
    (hpart : OriginalPlanarReadoutPartition (g ω) H (n ω) (t ω))
    (hc : ContinuousOn (g ω) (Icc (0:ℝ) 1))
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (hW : 0<W)
    (hbuffer : ∀ r, r∈Icc (0:ℝ) 1 →
      W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g ω r)) Eᶜ) :
    let d := D.direction (ω,D.index ω)
      let f := fun x => D.graph ((ω,D.index ω),x)
      let S := signedPlanarStrip (planarDirectionI d) (planarDirectionSign d)
        f (Icc (D.left ω) (D.right ω)) (W/4)
      S⊆E ∧ MeasurableSet S ∧
        volume.real S=(D.right ω-D.left ω)*W/2 ∧
        L ω*W/(8*(H : ℝ)*(K : ℝ))≤volume.real S := by
  let d := D.direction (ω,D.index ω)
  let f := fun x => D.graph ((ω,D.index ω),x)
  have hall := hpart.all_intervals hc (D.index ω)
  have hArc := D.arcs ω (D.index ω)
  have hprep := D.prepared ω
  have hinside := signedPlanarStrip_subset_of_half_width_buffer
    E (g ω) (t ω (D.index ω)) (t ω (D.index ω+1))
    (planarDirectionI d) (planarDirectionK d) (planarDirection_distinct d)
    (planarDirectionSign d) (planarDirection_sign d) f hArc.2.2.2.1
    (fun x hx => by
      obtain ⟨r,hr,he,_⟩ := hArc.2.2.2.2 x hx
      exact ⟨r,hr,he.symm⟩)
    W hW (fun r hr => hbuffer r
      ⟨hall.1.1.trans hr.1,hr.2.trans hall.2.1.2⟩)
  have hmeasure := signedPlanarStrip_measurable_volume (planarDirectionI d)
    (planarDirectionSign d) (planarDirection_sign d) f (D.left ω) (D.right ω)
    (W/4) hprep.2.2.2.1.continuousOn
  have harea := volume_real_signedPlanarStrip_quarter (planarDirectionI d)
    (planarDirectionSign d) (planarDirection_sign d) f (D.left ω) (D.right ω)
    W hprep.2.2.2.1.continuousOn hprep.1.le hW.le
  refine ⟨(signedPlanarStrip_mono_domain _ _ _ hprep.2.1 _).trans hinside,
    hmeasure.1,harea,?_⟩
  rw [harea]
  calc
    L ω*W/(8*(H : ℝ)*(K : ℝ)) =
        (L ω/(4*(H : ℝ)*(K : ℝ)))*W/2 := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ (D.right ω-D.left ω)*W/2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (D.macroscopic_length ω) hW.le) (by norm_num)

end PaperI
