import PaperILean.PlanarHalfOpenGrid

/-! I1261: count touched grid cells using the area of an actual enlargement,
not the area of the original set. Finiteness is proved from finite-subfamily
area bounds. Labels remain indices, so coincident points are not collapsed. -/

noncomputable section
namespace PaperI
open Set Metric MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planarGrid_finite_subset_area_bound (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ)
    {C : Set (EuclideanSpace ℝ (Fin 2))} {B : ℝ} (hB : 0 ≤ B)
    (harea : volume (cthickening (2*δ) C) ≤ ENNReal.ofReal B)
    (S : Finset (Fin 2 → ℤ)) (hS : (S : Set (Fin 2 → ℤ)) ⊆ planarGridTouched o δ C) :
    (S.card : ℝ)*δ^2 ≤ B := by
  have hvol : volume (⋃ k ∈ S, planarGridCell o δ k) = ENNReal.ofReal ((S.card : ℝ)*δ^2) := by
    rw [measure_biUnion_finset
      (fun i _ j _ hij => planarGridCell_pairwiseDisjoint o hδ hij)
      (fun k _ => measurableSet_planarGridCell o δ k)]
    simp [volume_planarGridCell o hδ.le,Finset.sum_const,nsmul_eq_mul,ENNReal.ofReal_mul]
  have hsub : (⋃ k ∈ S, planarGridCell o δ k) ⊆ cthickening (2*δ) C := by
    exact iUnion₂_subset fun k hk => touched_planarGridCell_subset_cthickening (hS hk)
  have h := (measure_mono hsub).trans harea
  rw [hvol] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

theorem planarGridTouched_finite_of_enlargement_area (o : Fin 2 → ℝ)
    {δ : ℝ} (hδ : 0 < δ) {C : Set (EuclideanSpace ℝ (Fin 2))} {B : ℝ} (hB : 0 ≤ B)
    (harea : volume (cthickening (2*δ) C) ≤ ENNReal.ofReal B) :
    (planarGridTouched o δ C).Finite := by
  by_contra hinf
  obtain ⟨N,hN⟩ := exists_nat_gt (B/δ^2)
  obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have h := (le_div_iff₀ (pow_pos hδ 2)).mpr
    (planarGrid_finite_subset_area_bound o hδ hB harea S hS)
  rw [hcard] at h
  exact (not_le_of_gt hN) h

theorem planarGrid_finite_cover_of_enlargement_area (o : Fin 2 → ℝ)
    {δ : ℝ} (hδ : 0 < δ) {C : Set (EuclideanSpace ℝ (Fin 2))} {B : ℝ} (hB : 0 ≤ B)
    (harea : volume (cthickening (2*δ) C) ≤ ENNReal.ofReal B) :
    ∃ S : Finset (Fin 2 → ℤ),
      (∀ k, k ∈ S ↔ k ∈ planarGridTouched o δ C) ∧
      C ⊆ ⋃ k ∈ S, planarGridCell o δ k ∧
      (⋃ k ∈ S, planarGridCell o δ k) ⊆ cthickening (2*δ) C ∧
      (S.card : ℝ) ≤ B/δ^2 := by
  classical
  let hfin := planarGridTouched_finite_of_enlargement_area o hδ hB harea
  refine ⟨hfin.toFinset,fun k => hfin.mem_toFinset,?_,?_,?_⟩
  · simpa only [hfin.mem_toFinset] using planarGridTouched_cover o hδ C
  · exact iUnion₂_subset fun k hk =>
      touched_planarGridCell_subset_cthickening (hfin.mem_toFinset.mp hk)
  · exact (le_div_iff₀ (pow_pos hδ 2)).mpr
      (planarGrid_finite_subset_area_bound o hδ hB harea hfin.toFinset
        (fun _ hk => hfin.mem_toFinset.mp hk))

theorem planarGrid_label_card_bound {ι : Type*} (J : Finset ι)
    (p : ι → EuclideanSpace ℝ (Fin 2)) (o : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin 2 → ℤ)) (hcover : ∀ i ∈ J, p i ∈ ⋃ k ∈ S, planarGridCell o δ k)
    {M : ℝ}
    (hlocal : ∀ k : Fin 2 → ℤ, ((J.filter (fun i => p i ∈ planarSquare (fun j => o j+(k j : ℝ)*δ) δ)).card : ℝ) ≤ M) :
    (J.card : ℝ) ≤ (S.card : ℝ)*M := by
  classical
  have hmaps : (J : Set ι).MapsTo (fun i => planarGridIndex o δ (p i)) S := by
    intro i hi
    obtain ⟨k,hk,hpk⟩ := mem_iUnion₂.mp (hcover i hi)
    simpa only [planarGridIndex_eq_of_mem hδ hpk] using hk
  have hfiber (k : Fin 2 → ℤ) :
      ((J.filter (fun i => planarGridIndex o δ (p i) = k)).card : ℝ) ≤ M := by
    refine le_trans ?_ (hlocal k)
    exact_mod_cast Finset.card_le_card (show
      J.filter (fun i => planarGridIndex o δ (p i) = k) ⊆
        J.filter (fun i => p i ∈ planarSquare (fun j => o j+(k j : ℝ)*δ) δ) from by
      intro i hi
      obtain ⟨hiJ,hik⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hiJ,planarGridCell_subset_square o δ k ?_⟩
      simpa only [hik] using mem_planarGridCell_index o hδ (p i))
  calc
    (J.card : ℝ) = ∑ k ∈ S, ((J.filter (fun i => planarGridIndex o δ (p i) = k)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _k ∈ S, M := Finset.sum_le_sum (fun k _ => hfiber k)
    _ = (S.card : ℝ)*M := by simp

end PaperI
