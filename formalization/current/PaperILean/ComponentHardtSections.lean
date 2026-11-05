import PaperILean.UniformComponentSignFormat
import PaperILean.FiniteConnectedCover

/-! Componentwise sections obtained by fixing reference-fiber representatives
in the actual semialgebraic Hardt charts. The atlas records the original
fibers, and no chart is presumed to be the identity at its base point. -/

noncomputable section
namespace PaperI
open Set

def componentSectionGraph {ρ κ : Type*} (U : Set (ρ → ℝ))
    (s : U → κ → ℝ) : Set ((ρ ⊕ κ) → ℝ) :=
  {v | ∃ hp : v ∘ Sum.inl ∈ U, v ∘ Sum.inr = s ⟨_, hp⟩}

def componentSectionRegion {ρ κ : Type*} (A : Set ((ρ ⊕ κ) → ℝ))
    (U : Set (ρ → ℝ)) (s : U → κ → ℝ) : Set ((ρ ⊕ κ) → ℝ) :=
  {v | ∃ hp : v ∘ Sum.inl ∈ U,
    v ∘ Sum.inr ∈ connectedComponentIn (projectionFiber A (v ∘ Sum.inl)) (s ⟨_, hp⟩)}

theorem subtype_mem_connectedComponentIn_iff {X : Type*} [TopologicalSpace X]
    {S : Set X} (x y : S) :
    y.val ∈ connectedComponentIn S x.val ↔
      ConnectedComponents.mk y = ConnectedComponents.mk x := by
  rw [connectedComponentIn_eq_image x.property]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h : z = y := Subtype.ext hzy
    exact ConnectedComponents.coe_eq_coe'.mpr (h ▸ hz)
  · intro h
    exact ⟨y, ConnectedComponents.coe_eq_coe'.mp h, rfl⟩

theorem componentSectionRegion_mem_iff {ρ κ : Type*}
    (A : Set ((ρ ⊕ κ) → ℝ)) (U : Set (ρ → ℝ)) (s : U → κ → ℝ)
    (hS : ∀ p : U, s p ∈ projectionFiber A p.val) (p : ρ → ℝ) (x : κ → ℝ) :
    Sum.elim p x ∈ componentSectionRegion A U s ↔
      ∃ hp : p ∈ U, ∃ hx : x ∈ projectionFiber A p,
        ConnectedComponents.mk (⟨x, hx⟩ : projectionFiber A p) =
          ConnectedComponents.mk (⟨s ⟨p, hp⟩, hS ⟨p, hp⟩⟩ : projectionFiber A p) := by
  change (∃ hp : p ∈ U, x ∈ connectedComponentIn (projectionFiber A p) (s ⟨p, hp⟩)) ↔ _
  constructor
  · rintro ⟨hp, hx⟩
    have hm := connectedComponentIn_subset (projectionFiber A p) (s ⟨p, hp⟩) hx
    exact ⟨hp, hm, (subtype_mem_connectedComponentIn_iff ⟨_, hS ⟨p, hp⟩⟩ ⟨_, hm⟩).mp hx⟩
  · rintro ⟨hp, hx, h⟩
    exact ⟨hp, (subtype_mem_connectedComponentIn_iff ⟨_, hS ⟨p, hp⟩⟩ ⟨_, hx⟩).mpr h⟩

structure ComponentSectionAtlas {ρ κ : Type*} (A : Set ((ρ ⊕ κ) → ℝ)) where
  n : ℕ
  piece : Fin n → Set (ρ → ℝ)
  piece_semialgebraic : ∀ i, HasPolynomialSignDescription (piece i)
  piece_subset : ∀ i, piece i ⊆ projectionDomain A
  cover : ∀ p ∈ projectionDomain A, ∃ i, p ∈ piece i
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  m : Fin n → ℕ
  sectionFn : ∀ i, Fin (m i) → piece i → κ → ℝ
  section_continuous : ∀ i j, Continuous (sectionFn i j)
  section_mem : ∀ i j p, sectionFn i j p ∈ projectionFiber A p.val
  component_bijective : ∀ i (p : piece i), Function.Bijective
    (fun j => ConnectedComponents.mk
      (⟨sectionFn i j p, section_mem i j p⟩ : projectionFiber A p.val))
  graph_semialgebraic : ∀ i j,
    HasPolynomialSignDescription (componentSectionGraph (piece i) (sectionFn i j))
  region_semialgebraic : ∀ i j,
    HasPolynomialSignDescription (componentSectionRegion A (piece i) (sectionFn i j))

def ProjectionHardtData.componentSection {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (x : projectionFiber A (D.basePoint i).val) : D.piece i → κ → ℝ :=
  fun p => (D.fiberHomeomorph i p x).val

theorem ProjectionHardtData.componentSection_continuous {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (x : projectionFiber A (D.basePoint i).val) :
    Continuous (D.componentSection i x) :=
  continuous_snd.comp (continuous_subtype_val.comp
    ((D.chart i).continuous.comp (continuous_id.prodMk continuous_const)))

theorem ProjectionHardtData.componentSectionGraph_eq_transport {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (x : projectionFiber A (D.basePoint i).val) :
    componentSectionGraph (D.piece i) (D.componentSection i x) =
      hardtTransportSet D i {x.val} := by
  ext v
  constructor
  · rintro ⟨hp, hy⟩
    exact ⟨x.val, rfl, hp, x.property, hy⟩
  · rintro ⟨y, hy, hp, hf, hz⟩
    rcases hy with rfl
    exact ⟨hp, hz⟩

theorem ProjectionHardtData.componentSectionRegion_eq_transport {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (x : projectionFiber A (D.basePoint i).val) :
    componentSectionRegion A (D.piece i) (D.componentSection i x) =
      hardtTransportSet D i
        (connectedComponentIn (projectionFiber A (D.basePoint i).val) x.val) := by
  ext v
  let p := v ∘ Sum.inl
  let y := v ∘ Sum.inr
  have hv : Sum.elim p y = v := by funext a; cases a <;> rfl
  rw [← hv, componentSectionRegion_mem_iff A (D.piece i) (D.componentSection i x)
    (fun q => (D.fiberHomeomorph i q x).property)]
  constructor
  · rintro ⟨hp, hy, hcomp⟩
    let e := D.fiberHomeomorph i ⟨p, hp⟩
    let z := e.symm ⟨y, hy⟩
    have hz : ConnectedComponents.mk z = ConnectedComponents.mk x := by
      apply (connectedComponentsEquivOfHomeomorph e).injective
      change ConnectedComponents.mk (e z) = ConnectedComponents.mk (e x)
      simpa only [z, Homeomorph.apply_symm_apply] using hcomp
    refine ⟨z.val, (subtype_mem_connectedComponentIn_iff x z).mpr hz, hp, z.property, ?_⟩
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)).symm
  · rintro ⟨z, hz, hp, hf, hy⟩
    let e := D.fiberHomeomorph i ⟨p, hp⟩
    let z' : projectionFiber A (D.basePoint i).val := ⟨z, hf⟩
    have hmem : y ∈ projectionFiber A p := by
      change y = (e z').val at hy
      rw [hy]
      exact (e z').property
    refine ⟨hp, hmem, ?_⟩
    have hcomp := (subtype_mem_connectedComponentIn_iff x z').mp hz
    have hm := congrArg (connectedComponentsEquivOfHomeomorph e) hcomp
    change ConnectedComponents.mk (e z') = ConnectedComponents.mk (e x) at hm
    have heq : (⟨y, hmem⟩ : projectionFiber A p) = e z' := Subtype.ext hy
    simpa only [heq] using hm

theorem published_component_section_atlas
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (A : Set ((ρ ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    Nonempty (ComponentSectionAtlas A) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hdom := published_real_projection_has_sign_description hQE
    (hasPolynomialSignDescription_definable hA)
  obtain ⟨D⟩ := hHardt.projection_trivialization A (fun _ => A) hA hdom
    (fun _ => hA) (fun _ => subset_rfl)
  let S (i : Fin D.n) := projectionFiber A (D.basePoint i).val
  letI (i : Fin D.n) : Finite (ConnectedComponents (S i)) :=
    published_finite_connectedComponents hCell.toFiniteConnectedCover (S i) (D.fiber_semialgebraic i)
  letI (i : Fin D.n) : Fintype (ConnectedComponents (S i)) := Fintype.ofFinite _
  let m (i : Fin D.n) := Fintype.card (ConnectedComponents (S i))
  let e (i : Fin D.n) : Fin (m i) ≃ ConnectedComponents (S i) :=
    (Fintype.equivFin _).symm
  let r (i : Fin D.n) (j : Fin (m i)) : S i :=
    (ConnectedComponents.surjective_coe (e i j)).choose
  have hr (i : Fin D.n) (j : Fin (m i)) : ConnectedComponents.mk (r i j) = e i j :=
    (ConnectedComponents.surjective_coe (e i j)).choose_spec
  have hcomp (i : Fin D.n) (x : κ → ℝ) :
      HasPolynomialSignDescription (connectedComponentIn (S i) x) := by
    obtain ⟨F, hF⟩ := D.fiber_semialgebraic i
    obtain ⟨_, _, h⟩ := published_bounded_sign_format_component_sign_format
      hCell hHardt hQE κ F.card (F.sup MvPolynomial.totalDegree)
    obtain ⟨B, _, _, hB⟩ := h F (S i) le_rfl (fun q hq => Finset.le_sup hq) hF
    exact ⟨B, hB x⟩
  have hsingle (x : κ → ℝ) : HasPolynomialSignDescription ({x} : Set (κ → ℝ)) := by
    apply hQE.finite_sign_description
    have h := realDefinable_finite_all (fun k : κ => realPolynomial_zero_definable
      (MvPolynomial.X k - MvPolynomial.C (x k) : MvPolynomial κ ℝ))
    simpa only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_eq_zero, ← funext_iff, Set.setOf_eq_eq_singleton] using h
  refine ⟨{
    n := D.n
    piece := D.piece
    piece_semialgebraic := D.piece_semialgebraic
    piece_subset := D.piece_subset
    cover := D.cover
    disjoint := D.disjoint
    m := m
    sectionFn := fun i j => D.toProjectionHardtData.componentSection i (r i j)
    section_continuous := fun i j => D.toProjectionHardtData.componentSection_continuous i (r i j)
    section_mem := fun i j p => (D.toProjectionHardtData.fiberHomeomorph i p (r i j)).property
    component_bijective := ?_
    graph_semialgebraic := ?_
    region_semialgebraic := ?_ }⟩
  · intro i p
    have heq : (fun j => ConnectedComponents.mk
        (D.toProjectionHardtData.fiberHomeomorph i p (r i j))) =
        (connectedComponentsEquivOfHomeomorph (D.toProjectionHardtData.fiberHomeomorph i p)) ∘ e i := by
      funext j
      change _ = (connectedComponentsEquivOfHomeomorph _ (e i j))
      rw [← hr i j]
      rfl
    change Function.Bijective (fun j => ConnectedComponents.mk
      (D.toProjectionHardtData.fiberHomeomorph i p (r i j)))
    rw [heq]
    exact (connectedComponentsEquivOfHomeomorph _).bijective.comp (e i).bijective
  · intro i j
    rw [D.toProjectionHardtData.componentSectionGraph_eq_transport]
    exact hQE.finite_sign_description _ (hardtTransportSet_definable D i (hsingle (r i j).val))
  · intro i j
    rw [D.toProjectionHardtData.componentSectionRegion_eq_transport]
    exact hQE.finite_sign_description _ (hardtTransportSet_definable D i (hcomp i (r i j).val))

end PaperI
