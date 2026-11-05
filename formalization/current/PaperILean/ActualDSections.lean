import PaperILean.UniformComponentSections
import PaperILean.FiniteDefinableSelection
import Mathlib.Algebra.MvPolynomial.CommRing

/-! I3239[0,170): actual fixed-d component sections and a fixed-order assignment.
The relation is literally E(g) and g3=t. All bounds precede the coefficients
and E. Assignment regions are pulled back from the joint component regions;
unique component eligibility makes the first-eligible rule exact. -/
noncomputable section
namespace PaperI.ActualDSections
open Set
open scoped BigOperators

/-- Actual original-coordinate relation over the d parameter. -/
def actualDRelation (E : Set (Fin 6 → ℝ)) : Set ((Fin 1 ⊕ Fin 6) → ℝ) :=
  {z | z ∘ Sum.inr ∈ E ∧ z (Sum.inr 3) = z (Sum.inl 0)}

@[simp] theorem actual_d_fiber (E : Set (Fin 6 → ℝ)) (t : ℝ) :
    projectionFiber (actualDRelation E) (fun _ => t) = {g | g ∈ E ∧ g 3 = t} := rfl

/-- Derive the parameterized relation's sign format from the ambient format. -/
theorem actual_d_relation_format
    (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ))
    (s D : ℕ) (hc : A.card ≤ s) (hd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hE : PolynomialSignDetermined A E) :
    HasBoundedSignFormat (s+1) (max D 1) (actualDRelation E) := by
  classical
  let q : MvPolynomial (Fin 1 ⊕ Fin 6) ℝ :=
    MvPolynomial.X (Sum.inr 3) - MvPolynomial.X (Sum.inl 0)
  let B := A.image (MvPolynomial.rename (Sum.inr : Fin 6 → Fin 1 ⊕ Fin 6))
  refine ⟨insert q B, (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans hc) 1), ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp [q])
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
      exact (MvPolynomial.totalDegree_rename_le _ r).trans ((hd r hr).trans (Nat.le_max_left D 1))
  · intro x y hxy
    have he : x ∘ Sum.inr ∈ E ↔ y ∘ Sum.inr ∈ E := by
      apply hE
      intro p hp
      have h := hxy (MvPolynomial.rename Sum.inr p)
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
      simpa only [MvPolynomial.eval_rename] using h
    have ht : x (Sum.inr 3) = x (Sum.inl 0) ↔
        y (Sum.inr 3) = y (Sum.inl 0) := by
      simpa only [q, map_sub, MvPolynomial.eval_X, sub_eq_zero] using
        (hxy q (Finset.mem_insert_self q B)).1
    exact and_congr he ht

/-- Coordinate substitution preserves the numerical sign-format budget. -/
theorem bounded_sign_format_preimage_comp {α β : Type*} (f : α → β)
    {s d : ℕ} {S : Set (α → ℝ)} (hS : HasBoundedSignFormat s d S) :
    HasBoundedSignFormat s d {x : β → ℝ | x ∘ f ∈ S} := by
  classical
  obtain ⟨A,hc,hd,hA⟩ := hS
  refine ⟨A.image (MvPolynomial.rename f), Finset.card_image_le.trans hc, ?_, ?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact (MvPolynomial.totalDegree_rename_le f q).trans (hd q hq)
  · intro x y hxy
    apply hA
    intro p hp
    have h := hxy (MvPolynomial.rename f p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    simpa only [MvPolynomial.eval_rename] using h

abbrev SectionLabel {E : Set (Fin 6 → ℝ)} (F : ComponentSectionAtlas (actualDRelation E)) :=
  Σ i : Fin F.n, Fin (F.m i)

/-- Eligibility means the actual state and the section point lie in the same
actual d fiber component. -/
def actualDRegion {E : Set (Fin 6 → ℝ)} (F : ComponentSectionAtlas (actualDRelation E))
    (q : SectionLabel F) : Set (Fin 6 → ℝ) :=
  {g | Sum.elim (fun _ : Fin 1 => g 3) g ∈
    componentSectionRegion (actualDRelation E) (F.piece q.1) (F.sectionFn q.1 q.2)}

theorem actual_d_region_subset {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (q : SectionLabel F) :
    actualDRegion F q ⊆ E := by
  intro g hg
  obtain ⟨hp,hx,heq⟩ := (componentSectionRegion_mem_iff (actualDRelation E) (F.piece q.1) (F.sectionFn q.1 q.2)
    (F.section_mem q.1 q.2) (fun _ => g 3) g).mp hg
  exact hx.1

theorem actual_d_region_cover {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (g : Fin 6 → ℝ) (hg : g ∈ E) :
    ∃ q : SectionLabel F, g ∈ actualDRegion F q := by
  have hf : g ∈ projectionFiber (actualDRelation E) (fun _ : Fin 1 => g 3) := ⟨hg,rfl⟩
  obtain ⟨i,hpi⟩ := F.cover (fun _ => g 3) ⟨g,hf⟩
  obtain ⟨j,hj⟩ := (F.component_bijective i ⟨_,hpi⟩).2
    (ConnectedComponents.mk ⟨g,hf⟩)
  refine ⟨⟨i,j⟩,?_⟩
  exact (componentSectionRegion_mem_iff (actualDRelation E) (F.piece i) (F.sectionFn i j) (F.section_mem i j) (fun _ => g 3) g).mpr
    ⟨hpi,hf,hj.symm⟩

theorem actual_d_region_unique {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) {g : Fin 6 → ℝ}
    {q r : SectionLabel F} (hq : g ∈ actualDRegion F q)
    (hr : g ∈ actualDRegion F r) : q = r := by
  rcases q with ⟨i,j⟩
  rcases r with ⟨i',j'⟩
  obtain ⟨hp,hx,heq⟩ := (componentSectionRegion_mem_iff (actualDRelation E) (F.piece i) (F.sectionFn i j)
    (F.section_mem i j) (fun _ => g 3) g).mp hq
  obtain ⟨hp',hx',heq'⟩ := (componentSectionRegion_mem_iff (actualDRelation E) (F.piece i') (F.sectionFn i' j')
    (F.section_mem i' j') (fun _ => g 3) g).mp hr
  have hi : i = i' := by
    by_contra h
    exact Set.disjoint_left.mp (F.disjoint h) hp hp'
  subst i'
  have hj : j = j' := (F.component_bijective i ⟨_,hp⟩).1 (heq.symm.trans heq')
  subst j'
  rfl

theorem actual_d_region_format {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) {N s d : ℕ}
    (hF : F.Bounded N s d) (q : SectionLabel F) :
    HasBoundedSignFormat s d (actualDRegion F q) := by
  let f : Fin 1 ⊕ Fin 6 → Fin 6 := Sum.elim (fun _ => 3) id
  have heq : {g : Fin 6 → ℝ | g ∘ f ∈
      componentSectionRegion (actualDRelation E) (F.piece q.1) (F.sectionFn q.1 q.2)} =
      actualDRegion F q := by
    ext g
    have hz : g ∘ f = Sum.elim (fun _ : Fin 1 => g 3) g := by
      funext a
      cases a <;> rfl
    simp only [actualDRegion, Set.mem_setOf_eq, hz]
  rw [← heq]
  exact bounded_sign_format_preimage_comp f (hF.region_format q.1 q.2)

/-- The chosen finite order is fixed before the state is assigned. -/
structure FixedOrderAssignment {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (s d : ℕ) where
  rank : SectionLabel F → ℕ
  rank_injective : Function.Injective rank
  pick : E → SectionLabel F
  pick_first : ∀ g, g.val ∈ firstFiniteEligible (actualDRegion F) rank (pick g)
  assignment_fiber : ∀ q,
    {g | ∃ hg : g ∈ E, pick ⟨g,hg⟩ = q} = firstFiniteEligible (actualDRegion F) rank q
  first_region : ∀ q, firstFiniteEligible (actualDRegion F) rank q = actualDRegion F q
  assignment_format : ∀ q,
    HasBoundedSignFormat s d {g | ∃ hg : g ∈ E, pick ⟨g,hg⟩ = q}

theorem exists_fixed_order_assignment {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) {N s d : ℕ}
    (hF : F.Bounded N s d) : Nonempty (FixedOrderAssignment F s d) := by
  classical
  let rank : SectionLabel F → ℕ := fun q => (Fintype.equivFin (SectionLabel F) q).val
  have hrank : Function.Injective rank := by
    intro q r h
    exact (Fintype.equivFin (SectionLabel F)).injective (Fin.ext h)
  have hfirst : ∀ q, firstFiniteEligible (actualDRegion F) rank q = actualDRegion F q := by
    intro q
    apply Set.Subset.antisymm (firstFiniteEligible_subset _ _ _)
    intro g hg
    refine ⟨hg,?_⟩
    intro r hr hgr
    have he := actual_d_region_unique F hgr hg
    subst r
    exact (lt_irrefl _ hr)
  have hex : ∀ g : E, ∃ q, g.val ∈ actualDRegion F q :=
    fun g => actual_d_region_cover F g.val g.property
  choose pick hpick using hex
  have hfiber : ∀ q, {g | ∃ hg : g ∈ E, pick ⟨g,hg⟩ = q} = actualDRegion F q := by
    intro q
    ext g
    constructor
    · rintro ⟨hg,he⟩
      simpa only [he] using hpick ⟨g,hg⟩
    · intro hg
      have hE := actual_d_region_subset F q hg
      exact ⟨hE,actual_d_region_unique F (hpick ⟨g,hE⟩) hg⟩
  refine ⟨⟨rank,hrank,pick,?_,?_,hfirst,?_⟩⟩
  · intro g
    rw [hfirst]
    exact hpick g
  · intro q
    rw [hfiber,hfirst]
  · intro q
    rw [hfiber]
    exact actual_d_region_format F hF q

/-- The complement of the actual projection image is the one additional
zero-section region completing the finite partition of the entire axis. -/
structure WholeAxisPartition {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (N s d : ℕ) : Prop where
  piece_count : F.n + 1 ≤ N + 1
  outside_format : HasBoundedSignFormat (N*s) d (projectionDomain (actualDRelation E))ᶜ
  cover_axis : ∀ p, p ∉ projectionDomain (actualDRelation E) ∨ ∃ i, p ∈ F.piece i
  outside_disjoint : ∀ i, Disjoint (projectionDomain (actualDRelation E))ᶜ (F.piece i)
  outside_empty : ∀ p, p ∉ projectionDomain (actualDRelation E) →
    projectionFiber (actualDRelation E) p = ∅

theorem whole_axis_partition {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) {N s d : ℕ}
    (hF : F.Bounded N s d) : WholeAxisPartition F N s d := by
  classical
  refine ⟨Nat.add_le_add_right hF.pieces_le 1, ?_, ?_, ?_, ?_⟩
  · choose C hc hd hdet using hF.piece_format
    let B := Finset.univ.biUnion C
    refine ⟨B, ?_, ?_, ?_⟩
    · calc
        B.card ≤ ∑ i : Fin F.n, (C i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin F.n, s := Finset.sum_le_sum (fun i _ => hc i)
        _ = F.n*s := by simp
        _ ≤ N*s := Nat.mul_le_mul_right s hF.pieces_le
    · intro q hq
      obtain ⟨i,hi,hqi⟩ := Finset.mem_biUnion.mp hq
      exact hd i q hqi
    · intro x y hxy
      have hp : ∀ i, x ∈ F.piece i ↔ y ∈ F.piece i := by
        intro i
        apply hdet i
        intro q hq
        exact hxy q (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hq⟩)
      apply not_congr
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := F.cover x hx
        exact F.piece_subset i ((hp i).mp hi)
      · intro hy
        obtain ⟨i,hi⟩ := F.cover y hy
        exact F.piece_subset i ((hp i).mpr hi)
  · intro p
    by_cases hp : p ∈ projectionDomain (actualDRelation E)
    · exact Or.inr (F.cover p hp)
    · exact Or.inl hp
  · intro i
    exact Set.disjoint_left.mpr (fun _ hp hi => hp (F.piece_subset i hi))
  · intro p hp
    exact Set.eq_empty_iff_forall_not_mem.mpr (fun _ hx => hp ⟨_,hx⟩)

/-- Complete actual componentwise section construction and fixed-order
assignment. N,sOut,dOut are chosen before every ambient coefficient and E. -/
theorem actual_d_sections_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ N sOut dOut : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∃ F : ComponentSectionAtlas (actualDRelation E),
        F.Bounded N sOut dOut ∧
        (∑ i : Fin F.n, F.m i) ≤ N*N ∧
        (∀ i j (p : F.piece i), F.sectionFn i j p ∈ E ∧
          (F.sectionFn i j p) 3 = p.val 0) ∧
        WholeAxisPartition F N sOut dOut ∧
        Nonempty (FixedOrderAssignment F sOut dOut) ∧
        ∀ t : ℝ, projectionFiber (actualDRelation E) (fun _ => t) =
          {g | g ∈ E ∧ g 3 = t} := by
  classical
  obtain ⟨N,sOut,dOut,h⟩ := published_bounded_sign_format_component_sections
    hCell hHardt hQE (Fin 1) (Fin 6) (s+1) (max D 1)
  refine ⟨N,sOut,dOut,?_⟩
  intro A E hc hd hE
  obtain ⟨B,hcB,hdB,hB⟩ := actual_d_relation_format A E s D hc hd hE
  obtain ⟨F,hF⟩ := h B (actualDRelation E) hcB hdB hB
  refine ⟨F,hF,?_,?_,whole_axis_partition F hF,exists_fixed_order_assignment F hF,actual_d_fiber E⟩
  · calc
      (∑ i : Fin F.n, F.m i) ≤ ∑ _i : Fin F.n, N :=
        Finset.sum_le_sum (fun i _ => hF.sections_le i)
      _ = F.n * N := by simp
      _ ≤ N*N := Nat.mul_le_mul_right N hF.pieces_le
  · intro i j p
    exact F.section_mem i j p

end PaperI.ActualDSections
