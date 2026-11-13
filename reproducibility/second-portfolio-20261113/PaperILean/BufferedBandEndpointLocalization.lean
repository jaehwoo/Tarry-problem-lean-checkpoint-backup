import PaperILean.PlanarRelativeEndpoints
import PaperILean.BufferedBandPreparedArc

/-! I1265: localize the actual component together with the unchanged small
rectangle or prepared transverse strip. Every anchor in the same component
has the same absolute constants. No joint Borel selection is asserted. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory

def BufferedBandEndpointControl (E : Set (EuclideanSpace ℝ (Fin 2)))
    (W : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ bufferedBandComponent E W z,
    bufferedBandComponent E W z ∪ S ⊆ closedBall a (2*bufferedComponentScale E W z) ∧
    volume (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S)) ≤
      ENNReal.ofReal (4*Real.pi*(bufferedComponentScale E W z)^2) ∧
    volume (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S)) ≠ ⊤ ∧
    volume.real (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S)) ≤
      4*Real.pi*(bufferedComponentScale E W z)^2

theorem bufferedBandEndpointControl_of_localization
    {E : Set (EuclideanSpace ℝ (Fin 2))} {W : ℝ} (hW : 0 ≤ W)
    {z : EuclideanSpace ℝ (Fin 2)} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : ∀ a ∈ bufferedBandComponent E W z,
      bufferedBandComponent E W z ∪ S ⊆ closedBall a (2*bufferedComponentScale E W z)) :
    BufferedBandEndpointControl E W z S := by
  intro a ha
  have hL : 0 ≤ bufferedComponentScale E W z := hW.trans (le_max_left _ _)
  have harea := planar_relative_endpoints_area hL (hS a ha)
  exact ⟨hS a ha,harea,planar_finite_real_area_of_outer_bound (by positivity) harea⟩

theorem signedPlanarStrip_subset_closedBall_of_centerline
    (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (J : Set ℝ) (w R : ℝ)
    (a : EuclideanSpace ℝ (Fin 2))
    (hcenter : ∀ q ∈ J, signedPlanarStripPoint i σ h q 0 ∈ closedBall a R) :
    signedPlanarStrip i σ h J w ⊆ closedBall a (R+w) := by
  rintro p ⟨q,hq,u,hu,rfl⟩
  have hc : dist (signedPlanarStripPoint i σ h q 0) a ≤ R := hcenter q hq
  change dist _ a ≤ _
  calc
    dist _ a ≤ dist _ (signedPlanarStripPoint i σ h q 0) +
        dist (signedPlanarStripPoint i σ h q 0) a := dist_triangle _ _ _
    _ ≤ R+w := by rw [signedPlanarStripPoint_dist]; linarith

theorem bufferedBand_signed_strip_endpoint_control
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 ≤ W) {z : EuclideanSpace ℝ (Fin 2)}
    (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (J : Set ℝ)
    (hcenter : ∀ q ∈ J, signedPlanarStripPoint i σ h q 0 ∈ bufferedBandComponent E W z) :
    BufferedBandEndpointControl E W z (signedPlanarStrip i σ h J (W/4)) := by
  apply bufferedBandEndpointControl_of_localization hW
  intro a ha
  have hC := bufferedBandComponent_subset_closedBall hE hW ha
  have hWL : W ≤ bufferedComponentScale E W z := le_max_left _ _
  have hL := hW.trans hWL
  apply union_subset
  · exact hC.trans (closedBall_subset_closedBall (by linarith))
  · exact (signedPlanarStrip_subset_closedBall_of_centerline i σ h J (W/4)
      (bufferedComponentScale E W z) a (fun q hq => hC (hcenter q hq))).trans
      (closedBall_subset_closedBall (by linarith))

theorem bufferedBand_small_rectangle_endpoint_control
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 ≤ W) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ bufferedDistanceBand E W) :
    BufferedBandEndpointControl E W z (bufferedPointRectangle z W) := by
  apply bufferedBandEndpointControl_of_localization hW
  intro a ha
  have hC := bufferedBandComponent_subset_closedBall hE hW ha
  have hza : dist z a ≤ bufferedComponentScale E W z := hC (mem_bufferedBandComponent hz)
  have hWL : W ≤ bufferedComponentScale E W z := le_max_left _ _
  have hL := hW.trans hWL
  apply union_subset
  · exact hC.trans (closedBall_subset_closedBall (by linarith))
  · intro p hp
    have hpz : dist p z ≤ W/2 := bufferedPointRectangle_subset_closedBall z W hp
    exact (dist_triangle p z a).trans (by linarith)

theorem bufferedBand_path_strip_endpoint_control
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : Bornology.IsBounded E)
    {W : ℝ} (hW : 0 ≤ W) {z : EuclideanSpace ℝ (Fin 2)}
    {a b : Fin 2 → ℝ} (γ : SemialgebraicUnitPath (bufferedBandCoordinates E W z) a b)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (i k : Fin 2) (hik : i ≠ k) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ)
    (he : ∀ t ∈ Icc u v, h (σ*γ.toFun t i)=γ.toFun t k)
    (ho : ∀ q ∈ Icc (σ*γ.toFun u i) (σ*γ.toFun v i),
      ∃ t ∈ Icc u v, σ*γ.toFun t i=q)
    (J : Set ℝ) (hJ : J ⊆ Icc (σ*γ.toFun u i) (σ*γ.toFun v i)) :
    BufferedBandEndpointControl E W z (signedPlanarStrip i σ h J (W/4)) := by
  apply bufferedBand_signed_strip_endpoint_control hE hW
  intro q hq
  obtain ⟨t,ht,hpoint⟩ := signedPlanarStripPoint_zero_eq_path γ.toFun u v i k hik σ hσ h he ho (hJ hq)
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
  obtain ⟨x,hx,hxt⟩ := γ.mapsTo htunit
  rw [← hxt,Equiv.symm_apply_apply] at hpoint
  exact hpoint ▸ hx

theorem bufferedBand_endpoint_family_area {ι : Type*}
    (E : ι → Set (EuclideanSpace ℝ (Fin 2))) (W : ι → ℝ)
    (z a : ι → EuclideanSpace ℝ (Fin 2)) (S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    {L : ℝ} (hL : 0 ≤ L)
    (hcontrol : ∀ i, BufferedBandEndpointControl (E i) (W i) (z i) (S i))
    (ha : ∀ i, a i ∈ bufferedBandComponent (E i) (W i) (z i))
    (hscale : ∀ i, bufferedComponentScale (E i) (W i) (z i) ≤ L) :
    volume (⋃ i, relativePlanarEndpoints (a i) (bufferedBandComponent (E i) (W i) (z i) ∪ S i)) ≤
      ENNReal.ofReal (4*Real.pi*L^2) ∧
    volume (⋃ i, relativePlanarEndpoints (a i) (bufferedBandComponent (E i) (W i) (z i) ∪ S i)) ≠ ⊤ ∧
    volume.real (⋃ i, relativePlanarEndpoints (a i) (bufferedBandComponent (E i) (W i) (z i) ∪ S i)) ≤
      4*Real.pi*L^2 := by
  apply planar_relative_endpoint_family_area a _ hL
  intro i
  exact ((hcontrol i (a i) (ha i)).1).trans
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (hscale i) (by norm_num)))

end PaperI
