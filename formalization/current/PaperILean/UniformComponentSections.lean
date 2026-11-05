import PaperILean.ComponentHardtSections
import PaperILean.FiniteSelectorGraphs
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple
import PaperILean.PublishedGeometricFiberBounds

/-! Uniform componentwise sections are obtained by applying the structural
construction once to the joint coefficient-and-base family. Specializing its
finite graph descriptions does not increase polynomial count or degree.
No quantitative strengthening of the published Hardt input is assumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def HasBoundedSignFormat {α : Type*} (s d : ℕ) (S : Set (α → ℝ)) : Prop :=
  ∃ B : Finset (MvPolynomial α ℝ), B.card ≤ s ∧
    (∀ q ∈ B, q.totalDegree ≤ d) ∧ PolynomialSignDetermined B S

theorem HasBoundedSignFormat.mono {α : Type*} {s d s' d' : ℕ}
    {S : Set (α → ℝ)} (h : HasBoundedSignFormat s d S)
    (hs : s ≤ s') (hd : d ≤ d') : HasBoundedSignFormat s' d' S := by
  obtain ⟨B,hB,hD,hS⟩ := h
  exact ⟨B,hB.trans hs,fun q hq => (hD q hq).trans hd,hS⟩

theorem HasBoundedSignFormat.fiber {α β : Type*} {s d : ℕ}
    {S : Set ((α ⊕ β) → ℝ)} (h : HasBoundedSignFormat s d S) (c : α → ℝ) :
    HasBoundedSignFormat s d (projectionFiber S c) := by
  obtain ⟨B,hB,hD,hS⟩ := h
  exact projectionFiber_has_bounded_sign_format c B S s d hB hD hS

structure ComponentSectionAtlas.Bounded {ι κ : Type*}
    {A : Set ((ι ⊕ κ) → ℝ)} (F : ComponentSectionAtlas A) (N s d : ℕ) : Prop where
  pieces_le : F.n ≤ N
  sections_le : ∀ i, F.m i ≤ N
  piece_format : ∀ i, HasBoundedSignFormat s d (F.piece i)
  graph_format : ∀ i j,
    HasBoundedSignFormat s d (componentSectionGraph (F.piece i) (F.sectionFn i j))
  region_format : ∀ i j,
    HasBoundedSignFormat s d (componentSectionRegion A (F.piece i) (F.sectionFn i j))

theorem ComponentSectionAtlas.Bounded.mono {ι κ : Type*}
    {A : Set ((ι ⊕ κ) → ℝ)} {F : ComponentSectionAtlas A} {N s d N' s' d' : ℕ}
    (h : F.Bounded N s d) (hN : N ≤ N') (hs : s ≤ s') (hd : d ≤ d') :
    F.Bounded N' s' d' :=
  ⟨h.pieces_le.trans hN,fun i => (h.sections_le i).trans hN,
    fun i => (h.piece_format i).mono hs hd,
    fun i j => (h.graph_format i j).mono hs hd,
    fun i j => (h.region_format i j).mono hs hd⟩

def componentSectionRegroup {τ ι κ : Type*}
    (A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)) : Set ((τ ⊕ (ι ⊕ κ)) → ℝ) :=
  {v | v ∘ Equiv.sumAssoc τ ι κ ∈ A}

theorem componentSectionRegroup_mem {τ ι κ : Type*}
    (A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)) (c : τ → ℝ) (v : (ι ⊕ κ) → ℝ) :
    Sum.elim c v ∈ componentSectionRegroup A ↔
      Sum.elim (Sum.elim c (v ∘ Sum.inl)) (v ∘ Sum.inr) ∈ A := by
  change (Sum.elim c v ∘ Equiv.sumAssoc τ ι κ) ∈ A ↔ _
  have h : Sum.elim c v ∘ Equiv.sumAssoc τ ι κ =
      Sum.elim (Sum.elim c (v ∘ Sum.inl)) (v ∘ Sum.inr) := by
    funext a
    rcases a with (a | a) | a <;> rfl
  rw [h]

theorem componentSectionRegroup_semialgebraic {τ ι κ : Type}
    [Finite τ] [Finite ι] [Finite κ] (hQE : PublishedRealSemialgebraicity)
    {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)} (hA : HasPolynomialSignDescription A) :
    HasPolynomialSignDescription (componentSectionRegroup A) :=
  hQE.finite_sign_description _
    ((hasPolynomialSignDescription_definable hA).preimage_comp (Equiv.sumAssoc τ ι κ))

def componentSectionSlice {τ ι κ : Type*}
    (A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)) (c : τ → ℝ) : Set ((ι ⊕ κ) → ℝ) :=
  {v | Sum.elim (Sum.elim c (v ∘ Sum.inl)) (v ∘ Sum.inr) ∈ A}

def componentSectionSliceFn {τ ι κ : Type*} {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)}
    (F : ComponentSectionAtlas A) (c : τ → ℝ) (i : Fin F.n) (j : Fin (F.m i)) :
    projectionFiber (F.piece i) c → κ → ℝ :=
  fun p => F.sectionFn i j ⟨Sum.elim c p.val,p.property⟩

theorem componentSectionSlice_graph {τ ι κ : Type*}
    {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)} (F : ComponentSectionAtlas A)
    (c : τ → ℝ) (i : Fin F.n) (j : Fin (F.m i)) :
    componentSectionGraph (projectionFiber (F.piece i) c) (componentSectionSliceFn F c i j) =
      projectionFiber (componentSectionRegroup
        (componentSectionGraph (F.piece i) (F.sectionFn i j))) c := by
  ext v
  change _ ↔ Sum.elim c v ∈ componentSectionRegroup _
  rw [componentSectionRegroup_mem]
  rfl

theorem componentSectionSlice_region {τ ι κ : Type*}
    {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)} (F : ComponentSectionAtlas A)
    (c : τ → ℝ) (i : Fin F.n) (j : Fin (F.m i)) :
    componentSectionRegion (componentSectionSlice A c)
      (projectionFiber (F.piece i) c) (componentSectionSliceFn F c i j) =
      projectionFiber (componentSectionRegroup
        (componentSectionRegion A (F.piece i) (F.sectionFn i j))) c := by
  ext v
  change _ ↔ Sum.elim c v ∈ componentSectionRegroup _
  rw [componentSectionRegroup_mem]
  rfl

def ComponentSectionAtlas.specialize {τ ι κ : Type}
    [Finite τ] [Finite ι] [Finite κ] (hQE : PublishedRealSemialgebraicity)
    {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)} (F : ComponentSectionAtlas A) (c : τ → ℝ) :
    ComponentSectionAtlas (componentSectionSlice A c) where
  n := F.n
  piece i := projectionFiber (F.piece i) c
  piece_semialgebraic i := projectionFiber_hasPolynomialSignDescription _
    (F.piece_semialgebraic i) c
  piece_subset i := by
    intro p hp
    obtain ⟨x,hx⟩ := F.piece_subset i hp
    exact ⟨x,hx⟩
  cover p hp := F.cover (Sum.elim c p) hp
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (F.disjoint hij) hpi hpj
  m := F.m
  sectionFn := componentSectionSliceFn F c
  section_continuous i j := by
    apply (F.section_continuous i j).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro a
    cases a with
    | inl a => exact continuous_const
    | inr a => exact (continuous_apply a).comp continuous_subtype_val
  section_mem i j p := F.section_mem i j ⟨Sum.elim c p.val,p.property⟩
  component_bijective i p := F.component_bijective i ⟨Sum.elim c p.val,p.property⟩
  graph_semialgebraic i j := by
    rw [componentSectionSlice_graph]
    exact projectionFiber_hasPolynomialSignDescription _
      (componentSectionRegroup_semialgebraic hQE (F.graph_semialgebraic i j)) c
  region_semialgebraic i j := by
    rw [componentSectionSlice_region]
    exact projectionFiber_hasPolynomialSignDescription _
      (componentSectionRegroup_semialgebraic hQE (F.region_semialgebraic i j)) c

theorem ComponentSectionAtlas.exists_uniform_slice_format {τ ι κ : Type}
    [Finite τ] [Finite ι] [Finite κ] (hQE : PublishedRealSemialgebraicity)
    {A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)} (F : ComponentSectionAtlas A) :
    ∃ N s d : ℕ, ∀ c : τ → ℝ, (F.specialize hQE c).Bounded N s d := by
  classical
  let J := Σ i : Fin F.n, Fin (F.m i)
  obtain ⟨sP,dP,hP⟩ := finite_sign_descriptions_common_format F.piece F.piece_semialgebraic
  let G : J → Set ((τ ⊕ (ι ⊕ κ)) → ℝ) :=
    fun j => componentSectionRegroup (componentSectionGraph (F.piece j.1) (F.sectionFn j.1 j.2))
  let H : J → Set ((τ ⊕ (ι ⊕ κ)) → ℝ) :=
    fun j => componentSectionRegroup (componentSectionRegion A (F.piece j.1) (F.sectionFn j.1 j.2))
  obtain ⟨sG,dG,hG⟩ := finite_sign_descriptions_common_format G
    (fun j => componentSectionRegroup_semialgebraic hQE (F.graph_semialgebraic j.1 j.2))
  obtain ⟨sH,dH,hH⟩ := finite_sign_descriptions_common_format H
    (fun j => componentSectionRegroup_semialgebraic hQE (F.region_semialgebraic j.1 j.2))
  let N := max F.n (Finset.univ.sup F.m)
  let s := max sP (max sG sH)
  let d := max dP (max dG dH)
  refine ⟨N,s,d,?_⟩
  intro c
  refine ⟨le_max_left _ _,fun i => ?_,?_,?_,?_⟩
  · exact (Finset.le_sup (f := F.m) (Finset.mem_univ i)).trans (le_max_right _ _)
  · intro i
    exact ((show HasBoundedSignFormat sP dP (F.piece i) from hP i).fiber c).mono
      (le_max_left _ _) (le_max_left _ _)
  · intro i j
    change HasBoundedSignFormat s d
      (componentSectionGraph (projectionFiber (F.piece i) c) (componentSectionSliceFn F c i j))
    rw [componentSectionSlice_graph]
    exact ((show HasBoundedSignFormat sG dG (G ⟨i,j⟩) from hG ⟨i,j⟩).fiber c).mono
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro i j
    change HasBoundedSignFormat s d
      (componentSectionRegion (componentSectionSlice A c)
        (projectionFiber (F.piece i) c) (componentSectionSliceFn F c i j))
    rw [componentSectionSlice_region]
    exact ((show HasBoundedSignFormat sH dH (H ⟨i,j⟩) from hH ⟨i,j⟩).fiber c).mono
      ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))

def componentSectionUniversalRelation (ι κ : Type) [Fintype ι] [Fintype κ]
    (s D : ℕ) (b : (Fin s → Bool × Bool) → Bool) :
    Set ((((Fin s × ((ι ⊕ κ) → Fin (D + 1))) ⊕ ι) ⊕ κ) → ℝ) :=
  {v | v ∘ (Equiv.sumAssoc (Fin s × ((ι ⊕ κ) → Fin (D + 1))) ι κ).symm ∈
    universalPolynomialBooleanSet (ι ⊕ κ) s D b}

theorem componentSectionUniversalRelation_semialgebraic
    (hQE : PublishedRealSemialgebraicity) (ι κ : Type) [Fintype ι] [Fintype κ]
    (s D : ℕ) (b : (Fin s → Bool × Bool) → Bool) :
    HasPolynomialSignDescription (componentSectionUniversalRelation ι κ s D b) :=
  hQE.finite_sign_description _
    ((hasPolynomialSignDescription_definable
      (universalPolynomialBooleanSet_hasPolynomialSignDescription (ι ⊕ κ) s D b)).preimage_comp
      (Equiv.sumAssoc (Fin s × ((ι ⊕ κ) → Fin (D + 1))) ι κ).symm)

theorem componentSectionUniversalRelation_slice
    (ι κ : Type) [Fintype ι] [Fintype κ] (s D : ℕ)
    (b : (Fin s → Bool × Bool) → Bool)
    (c : (Fin s × ((ι ⊕ κ) → Fin (D + 1))) → ℝ) :
    componentSectionSlice (componentSectionUniversalRelation ι κ s D b) c =
      projectionFiber (universalPolynomialBooleanSet (ι ⊕ κ) s D b) c := by
  ext v
  change (Sum.elim (Sum.elim c (v ∘ Sum.inl)) (v ∘ Sum.inr) ∘
    (Equiv.sumAssoc _ ι κ).symm) ∈ universalPolynomialBooleanSet (ι ⊕ κ) s D b ↔
      Sum.elim c v ∈ universalPolynomialBooleanSet (ι ⊕ κ) s D b
  have h : Sum.elim (Sum.elim c (v ∘ Sum.inl)) (v ∘ Sum.inr) ∘
      (Equiv.sumAssoc _ ι κ).symm = Sum.elim c v := by
    funext a
    rcases a with a | (a | a) <;> rfl
  rw [h]

theorem published_family_component_sections
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {τ ι κ : Type} [Finite τ] [Finite ι] [Finite κ]
    (A : Set (((τ ⊕ ι) ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ N s d : ℕ, ∀ c : τ → ℝ,
      ∃ F : ComponentSectionAtlas (componentSectionSlice A c), F.Bounded N s d := by
  obtain ⟨F⟩ := published_component_section_atlas hCell hHardt hQE A hA
  obtain ⟨N,s,d,h⟩ := F.exists_uniform_slice_format hQE
  exact ⟨N,s,d,fun c => ⟨F.specialize hQE c,h c⟩⟩

theorem bounded_component_sections_congr {ι κ : Type*}
    {A B : Set ((ι ⊕ κ) → ℝ)} {N s d : ℕ} (heq : A = B)
    (h : ∃ F : ComponentSectionAtlas A, F.Bounded N s d) :
    ∃ F : ComponentSectionAtlas B, F.Bounded N s d := heq ▸ h

theorem published_finite_family_component_sections
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {β τ ι κ : Type} [Fintype β] [Finite τ] [Finite ι] [Finite κ]
    (A : β → Set (((τ ⊕ ι) ⊕ κ) → ℝ)) (hA : ∀ b, HasPolynomialSignDescription (A b)) :
    ∃ N s d : ℕ, ∀ b (c : τ → ℝ),
      ∃ F : ComponentSectionAtlas (componentSectionSlice (A b) c), F.Bounded N s d := by
  classical
  choose N s d h using fun b => published_family_component_sections hCell hHardt hQE (A b) (hA b)
  refine ⟨Finset.univ.sup N,Finset.univ.sup s,Finset.univ.sup d,?_⟩
  intro b c
  obtain ⟨F,hF⟩ := h b c
  exact ⟨F,hF.mono (Finset.le_sup (f := N) (Finset.mem_univ b))
    (Finset.le_sup (f := s) (Finset.mem_univ b))
    (Finset.le_sup (f := d) (Finset.mem_univ b))⟩

theorem component_section_sign_image_decEq {α : Type*} (s : ℕ)
    (d₁ d₂ : DecidableEq (MvPolynomial α ℝ))
    (p : Fin s → MvPolynomial α ℝ) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined
      (@Finset.image (Fin s) (MvPolynomial α ℝ) d₁ p Finset.univ) S) :
    PolynomialSignDetermined
      (@Finset.image (Fin s) (MvPolynomial α ℝ) d₂ p Finset.univ) S := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact hS

theorem published_bounded_tuple_component_sections
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (ι κ : Type) [Fintype ι] [Fintype κ] (s D : ℕ) :
    ∃ N sOut dOut : ℕ, ∀ (p : Fin s → MvPolynomial (ι ⊕ κ) ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set ((ι ⊕ κ) → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S →
      ∃ F : ComponentSectionAtlas S, F.Bounded N sOut dOut := by
  classical
  let B := (Fin s → Bool × Bool) → Bool
  obtain ⟨N,sOut,dOut,hOut⟩ := published_finite_family_component_sections hCell hHardt hQE
    (fun b : B => componentSectionUniversalRelation ι κ s D b)
    (fun b => componentSectionUniversalRelation_semialgebraic hQE ι κ s D b)
  refine ⟨N,sOut,dOut,?_⟩
  intro p hp S hS
  obtain ⟨b,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S
    (component_section_sign_image_decEq s _ _ p S hS)
  let c := polynomialFamilyCoefficients D p
  have heq : componentSectionSlice (componentSectionUniversalRelation ι κ s D b) c = S := by
    rw [componentSectionUniversalRelation_slice]
    exact hEq.symm
  exact bounded_component_sections_congr heq (hOut b c)

theorem published_bounded_sign_format_component_sections
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (ι κ : Type) [Fintype ι] [Fintype κ] (s D : ℕ) :
    ∃ N sOut dOut : ℕ,
      ∀ (A : Finset (MvPolynomial (ι ⊕ κ) ℝ)) (S : Set ((ι ⊕ κ) → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∃ F : ComponentSectionAtlas S, F.Bounded N sOut dOut := by
  obtain ⟨N,sOut,dOut,h⟩ := published_bounded_tuple_component_sections hCell hHardt hQE ι κ s D
  refine ⟨N,sOut,dOut,?_⟩
  intro A S hc hd hS
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S (component_section_sign_image_decEq s _ _ p S hSp)

end PaperI
