import PaperILean.GoodStripFixedFormat
import PaperILean.GoodStripBounds
import PaperILean.GoodStripPlanarClosure

noncomputable section

namespace PaperI.GoodStrips

open Set MeasureTheory

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
open scoped ENNReal

/-- Good points may be retained in a common open locus on which all of the
original scalar functions are genuinely analytic. -/
theorem measurable_good_subset_analytic {ι : Type} [Fintype ι]
    (hNash : PublishedPiecewiseNashExtensions)
    (f : ι → ℝ × ℝ → ℝ) {R G : Set (ℝ × ℝ)} (hR : IsOpen R)
    (hgraph : ∀ i, HasPolynomialSignDescription (scalarGraph (f i) R))
    (hG : MeasurableSet G) (hsub : G ⊆ R) :
    ∃ H : Set (ℝ × ℝ), MeasurableSet H ∧ H ⊆ G ∧
      volume (G \ H) = 0 ∧ volume H = volume G ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ H ⊆ U ∧ ∀ i, AnalyticOnNhd ℝ (f i) U := by
  classical
  choose U hU using fun i => exists_open_full_measure_smooth hNash (f i) R hR (hgraph i)
  let V := ⋂ i, U i
  have ho : IsOpen V := isOpen_iInter_of_finite fun i => (hU i).1
  let H := G ∩ V
  have hHm : MeasurableSet H := hG.inter ho.measurableSet
  have hn : volume (G \ H) = 0 := by
    apply measure_mono_null (t := ⋃ i, R \ U i) _ (measure_iUnion_null fun i => (hU i).2.2.1)
    intro x hx
    have hm : x ∉ V := fun h => hx.2 ⟨hx.1,h⟩
    change x ∉ ⋂ i, U i at hm
    rw [mem_iInter] at hm
    push_neg at hm
    obtain ⟨i,hi⟩ := hm
    exact mem_iUnion.mpr ⟨i,hsub hx.1,hi⟩
  have hHsub : H ⊆ G := inter_subset_left
  have he : (G \ H) ∪ H = G := by
    ext z
    by_cases hz : z ∈ H
    · simp [hz,hHsub hz]
    · simp [hz]
  have hv : volume H = volume G := by
    rw [← he, measure_union disjoint_sdiff_left hHm, hn,zero_add]
  exact ⟨H,hHm,hHsub,hn,hv,V,ho,inter_subset_right,fun i x hx => (hU i).2.2.2 x (mem_iInter.mp hx i)⟩

private theorem graph_signed_rectangle {ι : Type} (hQE : PublishedRealSemialgebraicity)
    (f : ι → ℝ × ℝ → ℝ) (G : ι → Set (Fin 3 → ℝ)) (J : ι → Finset (MvPolynomial (Fin 3) ℝ))
    (hJG : ∀ i, PolynomialSignDetermined (J i) (G i))
    (x0 x1 y0 y1 : ℝ)
    (hG : ∀ i z, z ∈ Rect x0 x1 y0 y1 → ∀ w, ![z.1,z.2,w] ∈ G i ↔ w = f i z) :
    ∀ i, HasPolynomialSignDescription (scalarGraph (f i) (Rect x0 x1 y0 y1)) := by
  classical
  intro i
  let p : Fin 4 → ℝ := ![x0,x1,y0,y1]
  let B := boxFamily (0 : Fin 4) 1 2 3
  let F : Set (Fin 4 ⊕ Fin 3 → ℝ) := {v | v ∘ Sum.inr ∈ G i}
  have hB := boxFamily_definable (0 : Fin 4) 1 2 3
  have hF : (univ : Set ℝ).Definable FirstOrder.Language.ring F :=
    (hasPolynomialSignDescription_definable ⟨J i,hJG i⟩).preimage_comp Sum.inr
  have hR : planeFiber B p = Rect x0 x1 y0 y1 := boxFamily_fiber 0 1 2 3 p
  have hr : RealizesOn F p (f i) (planeFiber B p) := by
    intro z hz w
    change ![z.1,z.2,w] ∈ G i ↔ _
    exact hG i z (hR ▸ hz) w
  simpa only [hR] using scalarGraph_sign_of_realizesOn hQE hB hF p (f i) hr

/-- Paper I I3202–I3218(i),(ii). Fixed sign format and derivative order select
uniform constants before the actual scalar list, amplitudes, rectangle,
subset and relative measure. The actual mixed coordinate jets are evaluated on
a common analytic locus. I3217 is the companion endpoint
`PaperI.derivative_good_points_curved_strips` in GoodStripPlanarClosure. -/
theorem derivative_good_points_rectangle
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedPiecewiseNashExtensions)
    {ι : Type} [Fintype ι] (sA dA sG dG N : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
    ∀ (G : ι → Set (Fin 3 → ℝ)) (J : ι → Finset (MvPolynomial (Fin 3) ℝ)),
      (∀ i, (J i).card ≤ sG) → (∀ i q, q ∈ J i → q.totalDegree ≤ dG) →
      (∀ i, PolynomialSignDetermined (J i) (G i)) →
    ∀ (f : ι → ℝ × ℝ → ℝ) (M : ι → ℝ) (x0 x1 y0 y1 : ℝ),
      let R := Rect x0 x1 y0 y1
      let L := x1-x0
      let W := y1-y0
      x0 < x1 → y0 < y1 →
      (∀ i z, z ∈ R → ∀ w, ![z.1,z.2,w] ∈ G i ↔ w = f i z) →
      (∀ i, 0 ≤ M i) →
      ((∀ i z, z ∈ R → |f i z| ≤ M i) →
        ∀ ε : ℝ, 0 < ε →
        ∃ U : Set (ℝ × ℝ), MeasurableSet U ∧ U ⊆ R ∧
          volume (R \ U) ≤ ENNReal.ofReal (ε*L*W) ∧
          (∀ z ∈ U, ∀ i a b, a+b ≤ N →
            |Jet (f i) a b z| ≤ D*(1/min ε 1)^(4*N)*M i/(L^a*W^b)) ∧
          ∃ V : Set (ℝ × ℝ), IsOpen V ∧ U ⊆ V ∧ ∀ i, AnalyticOnNhd ℝ (f i) V) ∧
      (∀ (S : Set (Fin 2 → ℝ)) (F : Finset (MvPolynomial (Fin 2) ℝ)),
        F.card ≤ sA → (∀ q ∈ F, q.totalDegree ≤ dA) → PolynomialSignDetermined F S →
        ∀ A : Set (ℝ × ℝ), A = {z : ℝ × ℝ | ![z.1,z.2] ∈ S} ∩ R →
        (∀ i z, z ∈ A → |f i z| ≤ M i) →
        ∀ q : ℝ, 0 < q → q ≤ 1 → ENNReal.ofReal q * volume R ≤ volume A →
        ∃ U : Set (ℝ × ℝ), MeasurableSet U ∧ U ⊆ A ∧
          ENNReal.ofReal ((1/2)*q^(max 1 (4*N))*L*W) ≤ volume U ∧
          (∀ z ∈ U, ∀ i a b, a+b ≤ N →
            |Jet (f i) a b z| ≤ (D*2^(4*N))*(1/q)^(max 1 (4*N))*M i/(L^a*W^b)) ∧
          ∃ V : Set (ℝ × ℝ), IsOpen V ∧ U ⊆ V ∧ ∀ i, AnalyticOnNhd ℝ (f i) V) := by
  obtain ⟨D,hD,prep⟩ := derivative_good_points_fixed_format hDD hCell hHardt hQE hNash
    (ι := ι) sA dA sG dG N
  refine ⟨D,hD,?_⟩
  intro G J hJc hJd hJG f M x0 x1 y0 y1
  dsimp only
  intro hx hy hf hM
  let R := Rect x0 x1 y0 y1
  have ho : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hgraph := graph_signed_rectangle hQE f G J hJG x0 x1 y0 y1 hf
  constructor
  · intro hAmp ε hε
    have hsign : PolynomialSignDetermined (∅ : Finset (MvPolynomial (Fin 2) ℝ)) univ := by
      intro x y _
      simp
    have hprep := prep univ ∅ (by simp) (by simp) hsign G J hJc hJd hJG f M x0 x1 y0 y1
      hx hy hf hM (fun i z hz => hAmp i z hz.2)
    have hprep' : ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∃ U : Set (ℝ × ℝ), MeasurableSet U ∧ U ⊆ R ∧
          volume (R \ U) ≤ ENNReal.ofReal (η*(x1-x0)*(y1-y0)) ∧
          ∀ z ∈ U, ∀ i a b, a+b ≤ N →
            |Jet (f i) a b z| ≤ D*(1/η)^(4*N)*M i/((x1-x0)^a*(y1-y0)^b) := by
      simpa only [mem_univ, setOf_true, univ_inter] using hprep
    obtain ⟨U,hUm,hUR,hUV,hD'⟩ :=
      (rect_loss_and_partial_bounds N D (zero_le_one.trans hD) f M hM x0 x1 y0 y1 hx hy R Subset.rfl hprep').1 ε hε
    obtain ⟨H,hHm,hHU,hnull,_,hA⟩ := measurable_good_subset_analytic hNash f ho hgraph hUm hUR
    refine ⟨H,hHm,hHU.trans hUR,?_,fun z hz => hD' z (hHU hz),hA⟩
    have hs : R \ H ⊆ (R \ U) ∪ (U \ H) := by
      intro z hz
      by_cases hu : z ∈ U
      · exact Or.inr ⟨hu,hz.2⟩
      · exact Or.inl ⟨hz.1,hu⟩
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (by rw [hnull,add_zero]; exact hUV))
  · intro S F hFc hFd hFS A hA hAmp q hq hq1 hqR
    subst A
    let A := {z : ℝ × ℝ | ![z.1,z.2] ∈ S} ∩ R
    have hAR : A ⊆ R := inter_subset_right
    have hprep := prep S F hFc hFd hFS G J hJc hJd hJG f M x0 x1 y0 y1 hx hy hf hM hAmp
    obtain ⟨U,hUm,hUA,hUV,hD'⟩ :=
      (rect_loss_and_partial_bounds N D (zero_le_one.trans hD) f M hM x0 x1 y0 y1 hx hy A hAR hprep).2 q hq hq1 hqR
    obtain ⟨H,hHm,hHU,_,he,hA⟩ := measurable_good_subset_analytic hNash f ho hgraph hUm (hUA.trans hAR)
    exact ⟨H,hHm,hHU.trans hUA,he ▸ hUV,fun z hz => hD' z (hHU hz),hA⟩

end PaperI.GoodStrips
