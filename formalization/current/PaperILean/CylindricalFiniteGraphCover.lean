import PaperILean.CylindricalFiniteFiberSections
import PaperILean.PolynomialJointMeasurability

/-! A common finite graph cover, obtained from the original CAD input with all
parameter coordinates retained. Each chart is continuous on its own domain.
The structure deliberately does not assert that the base domains are planar
cells or that the charts continue through their boundaries. -/

noncomputable section
namespace PaperI
open Set FirstOrder MeasureTheory
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure CylindricalFiniteGraphCover {ρ : Type} (n : ℕ)
    (P : Set (ρ → ℝ)) (R : Set ((ρ ⊕ Fin n) → ℝ)) where
  count : ℕ
  domain : Fin count → Set (ρ → ℝ)
  sectionMap : Fin count → (ρ → ℝ) → Fin n → ℝ
  domain_subset : ∀ i, domain i ⊆ P
  domain_sign : ∀ i, HasPolynomialSignDescription (domain i)
  graph_sign : ∀ i, HasPolynomialSignDescription (selectedFunctionGraph (domain i) (sectionMap i))
  continuousOn : ∀ i, ContinuousOn (sectionMap i) (domain i)
  cover : ∀ p ∈ P, ∀ x, x ∈ projectionFiber R p ↔
    ∃ i, p ∈ domain i ∧ x = sectionMap i p

theorem published_cylindrical_finite_graph_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (R : Set ((ρ ⊕ Fin n) → ℝ))
    (hP : HasPolynomialSignDescription P) (hR : HasPolynomialSignDescription R)
    (hfin : ∀ p ∈ P, (projectionFiber R p).Finite) :
    Nonempty (CylindricalFiniteGraphCover n P R) := by
  classical
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE n P
    (cadUnpackedRelation n R) hP
    (hQE.finite_sign_description _ (cadUnpackedRelation_definable n
      (hasPolynomialSignDescription_definable hR)))
  let e : Fin (Fintype.card d.slicedLeaf) ≃ d.slicedLeaf := (Fintype.equivFin _).symm
  refine ⟨{ count := Fintype.card d.slicedLeaf
            domain := fun i => d.base (e i).val.1
            sectionMap := fun i => d.finiteFiberSection (e i)
            domain_subset := fun i => d.base_subset _
            domain_sign := fun i => hQE.finite_sign_description _ (d.base_definable _)
            graph_sign := fun i => hQE.finite_sign_description _ (d.finiteFiberSection_graph _)
            continuousOn := fun i => d.finiteFiberSection_continuousOn _
            cover := ?_ }⟩
  intro p hp x
  have hpack := cadPackedRelation_unpacked n R
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := d.slicedFiberCell_cover hp (by rwa [hpack])
    refine ⟨e.symm j,?_,?_⟩
    · have hb := hj.1
      simpa only [cadPack_base,e.apply_symm_apply] using hb
    · simpa only [e.apply_symm_apply] using d.finiteFiber_eq_section j
        (by rw [hpack]; exact hfin p hp) hj
  · rintro ⟨i,hi,rfl⟩
    have hx := d.slicedFiberCell_subset (e i) p (d.finiteFiberSection_mem (e i) hi)
    rwa [hpack] at hx

theorem CylindricalFiniteGraphCover.graph_union {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {R : Set ((ρ ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) :
    (⋃ i, selectedFunctionGraph (C.domain i) (C.sectionMap i)) =
      {v | v ∈ R ∧ v ∘ Sum.inl ∈ P} := by
  ext v
  simp only [mem_iUnion,selectedFunctionGraph,mem_setOf_eq]
  have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    funext i; cases i <;> rfl
  constructor
  · rintro ⟨i,hi,hx⟩
    have hp := C.domain_subset i hi
    have h := (C.cover _ hp (v ∘ Sum.inr)).mpr ⟨i,hi,hx.symm⟩
    change Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) ∈ R at h
    exact ⟨he ▸ h,hp⟩
  · rintro ⟨hv,hp⟩
    obtain ⟨i,hi,hx⟩ := (C.cover _ hp (v ∘ Sum.inr)).mp
      (by simpa only [projectionFiber,mem_setOf_eq,he] using hv)
    exact ⟨i,hi,hx.symm⟩

theorem CylindricalFiniteGraphCover.domain_measurable {ρ : Type} [Fintype ρ] {n : ℕ}
    {P : Set (ρ → ℝ)} {R : Set ((ρ ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) (i : Fin C.count) : MeasurableSet (C.domain i) := by
  convert hasPolynomialSignDescription_borel (C.domain_sign i)
  exact BorelSpace.measurable_eq

theorem CylindricalFiniteGraphCover.graph_measurable {ρ : Type} [Fintype ρ] {n : ℕ}
    {P : Set (ρ → ℝ)} {R : Set ((ρ ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) (i : Fin C.count) :
    MeasurableSet (selectedFunctionGraph (C.domain i) (C.sectionMap i)) := by
  convert hasPolynomialSignDescription_borel (C.graph_sign i)
  exact BorelSpace.measurable_eq

theorem CylindricalFiniteGraphCover.common_graph_format {ρ : Type} {n : ℕ}
    {P : Set (ρ → ℝ)} {R : Set ((ρ ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) :
    ∃ s d : ℕ, ∀ i, ∃ A : Finset (MvPolynomial (ρ ⊕ Fin n) ℝ),
      A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
      PolynomialSignDetermined A (selectedFunctionGraph (C.domain i) (C.sectionMap i)) :=
  finite_sign_descriptions_common_format _ C.graph_sign

theorem CylindricalFiniteGraphCover.section_measurable {ρ : Type} [Fintype ρ] {n : ℕ}
    {P : Set (ρ → ℝ)} {R : Set ((ρ ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) (i : Fin C.count) :
    Measurable (fun p : C.domain i => C.sectionMap i p) :=
  (C.continuousOn i).restrict.measurable

end PaperI
