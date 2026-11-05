import PaperILean.ActualSectionFactor
import PaperILean.ExceptionalDSections
import PaperILean.ExceptionalFiberPackingStage
import PaperILean.OriginalHaarWindowGluing
import PaperILean.SectionIntervalFlow

/-! Transport actual indexed labels through their common regular section.
All comparisons are relative; arbitrary common absolute frames cancel.
The actual section restriction, graph format and source windows are retained. -/
noncomputable section
open scoped BigOperators Topology Matrix.L2OpNorm
namespace PaperI.SectionIntervalTransport
open Set Matrix ActualDSections ExceptionalDSections
open RegularSectionDifferential RegularSectionRates

theorem matrixFullHSNorm_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixFullHSNorm (A * B) ≤ matrixFullHSNorm A * matrixFullHSNorm B := by
  apply (sq_le_sq₀ (matrixFullHSNorm_nonneg _)
    (mul_nonneg (matrixFullHSNorm_nonneg _) (matrixFullHSNorm_nonneg _))).mp
  rw [mul_pow]
  simp only [matrixFullHSNorm_sq, Matrix.mul_apply]
  calc
    (∑ i, ∑ j, (∑ l, A i l * B l j) ^ 2) ≤
        ∑ i, ∑ j, (∑ l, (A i l) ^ 2) * (∑ l, (B l j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun l => B l j)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm

def relativeMatrixSize (a b : Fin 6 → ℝ) : ℝ :=
  matrixFullHSNorm (originalAffineHomogeneousMatrix (originalUpperRelativeFrame a b)) +
    matrixFullHSNorm (originalAffineHomogeneousMatrix (originalUpperRelativeFrame b a))

theorem relativeMatrixSize_eq (a b : Fin 6 → ℝ) :
    relativeMatrixSize a b =
      matrixFullHSNorm ((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b) +
        matrixFullHSNorm (((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b)⁻¹) := by
  rw [originalAffineHomogeneousMatrix_relative, originalAffineHomogeneousMatrix_inverse,
    ← originalUpperRelativeFrame_reverse]
  rfl

theorem relativeMatrixSize_nonneg (a b : Fin 6 → ℝ) : 0 ≤ relativeMatrixSize a b :=
  add_nonneg (matrixFullHSNorm_nonneg _) (matrixFullHSNorm_nonneg _)

theorem relativeMatrixSize_symm (a b : Fin 6 → ℝ) :
    relativeMatrixSize a b = relativeMatrixSize b a := add_comm _ _

theorem relativeMatrixSize_comp_le (a b c : Fin 6 → ℝ) :
    relativeMatrixSize a c ≤ relativeMatrixSize a b * relativeMatrixSize b c := by
  have hf := matrixFullHSNorm_mul_le
    (originalAffineHomogeneousMatrix (originalUpperRelativeFrame a b))
    (originalAffineHomogeneousMatrix (originalUpperRelativeFrame b c))
  have hr := matrixFullHSNorm_mul_le
    (originalAffineHomogeneousMatrix (originalUpperRelativeFrame c b))
    (originalAffineHomogeneousMatrix (originalUpperRelativeFrame b a))
  rw [← originalAffineHomogeneousMatrix_comp, originalUpperRelativeFrame_comp] at hf hr
  dsimp [relativeMatrixSize]
  have h1 := mul_nonneg
    (matrixFullHSNorm_nonneg (originalAffineHomogeneousMatrix (originalUpperRelativeFrame a b)))
    (matrixFullHSNorm_nonneg (originalAffineHomogeneousMatrix (originalUpperRelativeFrame c b)))
  have h2 := mul_nonneg
    (matrixFullHSNorm_nonneg (originalAffineHomogeneousMatrix (originalUpperRelativeFrame b a)))
    (matrixFullHSNorm_nonneg (originalAffineHomogeneousMatrix (originalUpperRelativeFrame b c)))
  nlinarith only [hf, hr, h1, h2]

theorem relative_neighborhood_three_links (a s t b : Fin 6 → ℝ)
    (P eF eS : ℝ) (hP : 0 < P)
    (ha : relativeMatrixSize s a ≤ P ^ eF)
    (hs : relativeMatrixSize s t ≤ P ^ eS)
    (hb : relativeMatrixSize t b ≤ P ^ eF) :
    ExceptionalFiberPackingStage.relativeNeighborhoodRadius a b ≤ P ^ (2 * eF + eS) := by
  apply ExceptionalPackingBounds.literal_relative_neighborhood_le a b
  rw [← relativeMatrixSize_eq]
  have ha' : relativeMatrixSize a s ≤ P ^ eF := by
    simpa only [relativeMatrixSize_symm a s] using ha
  calc
    relativeMatrixSize a b ≤ relativeMatrixSize a s * relativeMatrixSize s b :=
      relativeMatrixSize_comp_le a s b
    _ ≤ (P ^ eF) * ((P ^ eS) * (P ^ eF)) := by
      apply mul_le_mul ha' _ (relativeMatrixSize_nonneg _ _) (Real.rpow_nonneg hP.le _)
      exact (relativeMatrixSize_comp_le s t b).trans
        (mul_le_mul hs hb (relativeMatrixSize_nonneg _ _) (Real.rpow_nonneg hP.le _))
    _ = _ := by rw [← Real.rpow_add hP, ← Real.rpow_add hP]; congr 1; ring

private theorem cell_open_neighborhood (C L : Finset ℝ) (x y : ℝ)
    (hx : x ∈ axisCutCell C L) (hy : y ∈ axisCutCell C L) :
    ∃ a z : ℝ, x ∈ Ioo a z ∧ y ∈ Ioo a z ∧ Ioo a z ⊆ axisCutCell C L := by
  have hmin : min x y ∈ axisCutCell C L := by
    rcases le_total x y with h | h
    · simpa only [min_eq_left h] using hx
    · simpa only [min_eq_right h] using hy
  have hmax : max x y ∈ axisCutCell C L := by
    rcases le_total x y with h | h
    · simpa only [max_eq_right h] using hy
    · simpa only [max_eq_left h] using hx
  obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((axisCutCell_open C L).mem_nhds hmin)
  obtain ⟨u,v,huv,hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((axisCutCell_open C L).mem_nhds hmax)
  let a := (l + min x y) / 2
  let z := (max x y + v) / 2
  have ha : a ∈ axisCutCell C L := hsub ⟨by dsimp [a]; linarith [hlr.1],
    by dsimp [a]; linarith [hlr.1,hlr.2]⟩
  have hz : z ∈ axisCutCell C L := hsub' ⟨by dsimp [z]; linarith [huv.1,huv.2],
    by dsimp [z]; linarith [huv.2]⟩
  have hal : a < min x y := by dsimp [a]; linarith [hlr.1]
  have hzr : max x y < z := by dsimp [z]; linarith [huv.2]
  refine ⟨a,z,⟨hal.trans_le (min_le_left _ _),(le_max_left _ _).trans_lt hzr⟩,
    ⟨hal.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt hzr⟩,?_⟩
  intro w hw
  rw [mem_axisCutCell] at ha hz ⊢
  intro c hc
  by_cases hcl : c ∈ L
  · simpa only [if_pos hcl] using lt_trans (by simpa only [if_pos hcl] using ha c hc) hw.1
  · simpa only [if_neg hcl] using lt_trans hw.2 (by simpa only [if_neg hcl] using hz c hc)

private def sectionExtension {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) (t : ℝ) : Fin 6 → ℝ := by
  classical
  exact if ht : t ∈ axisCutCell C L then
    restrictSection F i j C L hU ⟨fun _ => t,ht⟩ else 0

private theorem sectionExtension_eq {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) (t : ℝ)
    (ht : t ∈ axisCutCell C L) :
    sectionExtension F i j C L hU t = restrictSection F i j C L hU ⟨fun _ => t,ht⟩ := by
  simp only [sectionExtension, dif_pos ht]

private theorem sectionExtension_continuousOn {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) :
    ContinuousOn (sectionExtension F i j C L hU) (axisCutCell C L) := by
  let f : axisCutCell C L → parameterCell C L := fun t => ⟨fun _ => t.val,t.property⟩
  have hf : Continuous f := by fun_prop
  have hc := (restrictSection_continuous F i j C L hU).comp hf
  apply continuousOn_iff_continuous_restrict.mpr
  convert hc using 1
  ext t a
  simp only [Set.restrict_apply, Function.comp_apply, sectionExtension_eq F i j C L hU t.val t.property]
  rfl

private theorem sectionExtension_graph {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) (s D : ℕ)
    (hfmt : HasBoundedSignFormat s D
      (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU))) :
    ∃ (Γ : Set ((Unit ⊕ Fin 6) → ℝ))
      (AΓ : Finset (MvPolynomial (Unit ⊕ Fin 6) ℝ)),
      AΓ.card ≤ s ∧ (∀ p ∈ AΓ,p.totalDegree ≤ D) ∧ PolynomialSignDetermined AΓ Γ ∧
      ∀ t ∈ axisCutCell C L, ∀ v : Fin 6 → ℝ,
        Sum.elim (fun _ : Unit => t) v ∈ Γ ↔ v = sectionExtension F i j C L hU t := by
  let f : Fin 1 ⊕ Fin 6 → Unit ⊕ Fin 6 := Sum.map (fun _ => ()) id
  let Γ : Set ((Unit ⊕ Fin 6) → ℝ) :=
    {v | v ∘ f ∈ componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)}
  obtain ⟨A,hAc,hAd,hA⟩ := bounded_sign_format_preimage_comp f hfmt
  refine ⟨Γ,A,hAc,hAd,hA,?_⟩
  intro t ht v
  rw [sectionExtension_eq F i j C L hU t ht]
  change (∃ hp : (Sum.elim (fun _ : Unit => t) v ∘ f) ∘ Sum.inl ∈ parameterCell C L,
    (Sum.elim (fun _ : Unit => t) v ∘ f) ∘ Sum.inr =
      restrictSection F i j C L hU ⟨_,hp⟩) ↔ _
  have hi : (Sum.elim (fun _ : Unit => t) v ∘ f) ∘ Sum.inl = (fun _ : Fin 1 => t) := rfl
  have ho : (Sum.elim (fun _ : Unit => t) v ∘ f) ∘ Sum.inr = v := rfl
  simp only [hi,ho]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨ht,h⟩⟩

/-- The actual restricted section on any open axis cell has a uniform relative
bound between all pairs at parameter distance at most one. The arbitrary
extension outside the cell is used only on an interior neighborhood. -/
theorem actual_restricted_section_interval_relative
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (E : Set (Fin 6 → ℝ)) (F : ComponentSectionAtlas (actualDRelation E))
      (C L : Finset ℝ) (i : Fin F.n) (j : Fin (F.m i))
      (hU : parameterCell C L ⊆ F.piece i),
      2 ≤ P → HasBoundedSignFormat s D
        (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)) →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P ^ Cw) →
      (∀ g ∈ E, P ^ (-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ (x y : ℝ) (hx : x ∈ axisCutCell C L) (hy : y ∈ axisCutCell C L),
      |y-x| ≤ 1 →
      relativeMatrixSize (restrictSection F i j C L hU ⟨fun _ => x,hx⟩)
        (restrictSection F i j C L hU ⟨fun _ => y,hy⟩) ≤
          P ^ (9 * ((N : ℝ) + max Cs 0 + 2 * max Cw 0 + 1) + 15) := by
  obtain ⟨N,hN⟩ := SectionIntervalFlow.actual_section_interval_relative
    hCell hHardt hQE hNash hPiece k s D hk
  refine ⟨N,?_⟩
  intro P Cs Cw S0 E F C L i j hU hP hfmt hwindow hpivot x y hx hy hxy
  obtain ⟨a,z,hxa,hya,hinside⟩ := cell_open_neighborhood C L x y hx hy
  obtain ⟨Γ,A,hAc,hAd,hA,hgraph⟩ := sectionExtension_graph F i j C L hU s D hfmt
  let g := sectionExtension F i j C L hU
  have hg (t : ℝ) (ht : t ∈ axisCutCell C L) : g t ∈ E ∧ g t 3 = t := by
    dsimp only [g]
    rw [sectionExtension_eq F i j C L hU t ht]
    exact F.section_mem i j ⟨fun _ => t,hU ht⟩
  have h := hN P Cs Cw S0 g Γ A a z x y hP
    ((sectionExtension_continuousOn F i j C L hU).mono hinside)
    hAc hAd hA (fun t ht => hgraph t (hinside ht))
    (fun t ht => (hg t (hinside ht)).2)
    (fun t ht => hwindow (g t) (hg t (hinside ht)).1)
    (fun t ht => hpivot (g t) (hg t (hinside ht)).1) hxa hya hxy
  dsimp only at h
  rw [← relativeMatrixSize_eq] at h
  simpa only [g,sectionExtension_eq F i j C L hU x hx,
    sectionExtension_eq F i j C L hU y hy] using h

private theorem actual_attachment_relative {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (C L : Finset ℝ)
    (i : Fin F.n) (j : Fin (F.m i)) (hU : parameterCell C L ⊆ F.piece i)
    (g u : Fin 6 → ℝ) (hgc : g 3 ∈ axisCutCell C L)
    (hp : (fun _ : Fin 1 => g 3) ∈ F.piece i) (R : ℝ)
    (hu : u = originalUpperRelativeFrame (F.sectionFn i j ⟨fun _ => g 3,hp⟩) g)
    (hb : matrixFullHSNorm (originalAffineHomogeneousMatrix u) +
      matrixFullHSNorm (originalAffineHomogeneousMatrix u)⁻¹ ≤ R) :
    relativeMatrixSize (restrictSection F i j C L hU ⟨fun _ => g 3,hgc⟩) g ≤ R := by
  rw [relativeMatrixSize_eq, originalAffineHomogeneousMatrix_relative]
  simpa only [hu,restrictSection] using hb

/-- Actual original labels in one section class and one open cut cell lie in
one polynomial relative affine neighborhood over a unit parameter interval.
Both attachment factors and the moving-section comparison are derived. -/
theorem actual_section_class_radius
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D sG DG : ℕ) (hk : 2 ≤ k) :
    ∃ M N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      2 ≤ P → A.card ≤ s → (∀ p ∈ A,p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P ^ Cw) →
      (∀ g ∈ E, P ^ (-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ (F : ComponentSectionAtlas (actualDRelation E)) (C L : Finset ℝ)
        (i : Fin F.n) (j : Fin (F.m i)) (hU : parameterCell C L ⊆ F.piece i),
        HasBoundedSignFormat sG DG
          (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)) →
      ∀ (g h : Fin 6 → ℝ), g ∈ actualDRegion F ⟨i,j⟩ → h ∈ actualDRegion F ⟨i,j⟩ →
        g 3 ∈ axisCutCell C L → h 3 ∈ axisCutCell C L → |h 3-g 3| ≤ 1 →
      ExceptionalFiberPackingStage.relativeNeighborhoodRadius g h ≤
        P ^ (2 * ((M : ℝ) * (6 * (Fintype.card (AugmentedCoordinateIndex k) : ℝ) +
          3 * max Cs 0 + 3 * max Cw 0 + 4) + 5) +
          (9 * ((N : ℝ) + max Cs 0 + 2 * max Cw 0 + 1) + 15)) := by
  obtain ⟨M,hM⟩ := ActualSectionFactor.actual_component_section_factor
    hCell hPath hHardt hQE hNash hPiece k s D hk
  obtain ⟨N,hN⟩ := actual_restricted_section_interval_relative
    hCell.toFiniteConnectedCover hHardt.toHardtTriviality hQE hNash hPiece k sG DG hk
  refine ⟨M,N,?_⟩
  intro P Cs Cw S0 A E hP hAc hAd hAE hwindow hpivot F C L i j hU hfmt g h hg hh hgc hhc hlen
  obtain ⟨hpg,hvg,hdg,ug,hug,hcompg,hdug,hboundg⟩ :=
    hM P Cs Cw S0 A E hP hAc hAd hAE hwindow hpivot F ⟨i,j⟩ g hg
  obtain ⟨hph,hvh,hdh,uh,huh,hcomph,hduh,hboundh⟩ :=
    hM P Cs Cw S0 A E hP hAc hAd hAE hwindow hpivot F ⟨i,j⟩ h hh
  let sg := restrictSection F i j C L hU ⟨fun _ => g 3,hgc⟩
  let sh := restrictSection F i j C L hU ⟨fun _ => h 3,hhc⟩
  have hbg := actual_attachment_relative F C L i j hU g ug hgc hpg _ hug hboundg
  have hbh := actual_attachment_relative F C L i j hU h uh hhc hph _ huh hboundh
  have hs := hN P Cs Cw S0 E F C L i j hU hP hfmt hwindow hpivot
    (g 3) (h 3) hgc hhc hlen
  exact relative_neighborhood_three_links g sg sh h P _ _ (by linarith) hbg hs hbh

end PaperI.SectionIntervalTransport
