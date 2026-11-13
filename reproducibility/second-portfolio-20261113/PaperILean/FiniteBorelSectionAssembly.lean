import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Measurable assembly of dependent local sections. The domain may be the actual
projection image of a relation. No value outside that domain, inhabited codomain,
compactness, or compatibility of overlapping local sections is required. -/

noncomputable section

namespace PaperI

open Set

/-- Disjoint measurable pieces allow dependent local sections to be glued without
choosing an arbitrary default value in the codomain. -/
theorem exists_measurable_section_of_countable_disjoint_cover
    {D X ι : Type*} [MeasurableSpace D] [MeasurableSpace X] [Countable ι]
    (U : ι → Set D) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ∀ d, ∃ i, d ∈ U i) (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (s : ∀ i, U i → X) (hs : ∀ i, Measurable (s i))
    (R : D → X → Prop) (hR : ∀ i (d : U i), R d.val (s i d)) :
    ∃ σ : D → X, Measurable σ ∧ ∀ d, R d (σ d) := by
  classical
  have hcompat : ∀ (i j) (d : D) (hi : d ∈ U i) (hj : d ∈ U j),
      s i ⟨d, hi⟩ = s j ⟨d, hj⟩ := by
    intro i j d hi hj
    by_cases hij : i = j
    · subst j
      rfl
    · exact False.elim ((Set.disjoint_left.mp (hdisjoint hij)) hi hj)
  have hUnion : ⋃ i, U i = Set.univ := by
    ext d
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover d
  refine ⟨Set.liftCover U s hcompat hUnion,
    measurable_liftCover U hU s hs hcompat hUnion, ?_⟩
  intro d
  obtain ⟨i, hi⟩ := hcover d
  rw [Set.liftCover_of_mem hi]
  exact hR i ⟨d, hi⟩

/-- A countable measurable cover can be made disjoint by choosing the least encoded
index. Thus local sections need not agree on overlaps. -/
theorem exists_measurable_section_of_countable_cover
    {D X ι : Type*} [MeasurableSpace D] [MeasurableSpace X] [Countable ι]
    (U : ι → Set D) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ∀ d, ∃ i, d ∈ U i)
    (s : ∀ i, U i → X) (hs : ∀ i, Measurable (s i))
    (R : D → X → Prop) (hR : ∀ i (d : U i), R d.val (s i d)) :
    ∃ σ : D → X, Measurable σ ∧ ∀ d, R d (σ d) := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat ι
  let V : ι → Set D := fun i => U i \ ⋃ j, ⋃ (_ : code j < code i), U j
  have hV : ∀ i, MeasurableSet (V i) := fun i =>
    (hU i).diff (.iUnion fun j => .iUnion fun _ => hU j)
  have hVU (i : ι) : V i ⊆ U i := fun _ hd => hd.1
  have hVcover : ∀ d, ∃ i, d ∈ V i := by
    intro d
    have hex : ∃ n : ℕ, ∃ i, code i = n ∧ d ∈ U i := by
      obtain ⟨i, hi⟩ := hcover d
      exact ⟨code i, i, rfl, hi⟩
    obtain ⟨i, hi, hd⟩ := Nat.find_spec hex
    refine ⟨i, hd, ?_⟩
    intro hmem
    rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hlt, hjd⟩
    have hmin : Nat.find hex ≤ code j := Nat.find_min' hex ⟨j, rfl, hjd⟩
    exact (not_lt_of_ge hmin) (hi ▸ hlt)
  have hVdisjoint : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro d hdi hdj
    have hne : code i ≠ code j := fun h => hij (hcode h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hdj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hlt, hdi.1⟩⟩)
    · exact hdi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hgt, hdj.1⟩⟩)
  let t : ∀ i, V i → X := fun i d => s i ⟨d.val, hVU i d.property⟩
  have ht : ∀ i, Measurable (t i) := fun i =>
    (hs i).comp (measurable_inclusion (hVU i))
  exact exists_measurable_section_of_countable_disjoint_cover V hV hVcover hVdisjoint
    t ht R (fun i d => hR i ⟨d.val, hVU i d.property⟩)

/-- Finite covers are the specialization used for finite Hardt decompositions. -/
theorem exists_measurable_section_of_finite_cover
    {D X ι : Type*} [MeasurableSpace D] [MeasurableSpace X] [Finite ι]
    (U : ι → Set D) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ∀ d, ∃ i, d ∈ U i)
    (s : ∀ i, U i → X) (hs : ∀ i, Measurable (s i))
    (R : D → X → Prop) (hR : ∀ i (d : U i), R d.val (s i d)) :
    ∃ σ : D → X, Measurable σ ∧ ∀ d, R d (σ d) :=
  exists_measurable_section_of_countable_cover U hU hcover s hs R hR

/-- The relation-preserving selector is defined exactly on the projection image,
including an empty image. There is no assertion about points outside that image. -/
theorem exists_measurable_section_on_projection_of_countable_cover
    {Z X ι : Type*} [MeasurableSpace Z] [MeasurableSpace X] [Countable ι]
    (R : Z → X → Prop)
    (U : ι → Set {z : Z // ∃ x : X, R z x})
    (hU : ∀ i, MeasurableSet (U i))
    (hcover : ∀ d, ∃ i, d ∈ U i)
    (s : ∀ i, U i → X) (hs : ∀ i, Measurable (s i))
    (hR : ∀ i (d : U i), R d.val.val (s i d)) :
    ∃ σ : {z : Z // ∃ x : X, R z x} → X,
      Measurable σ ∧ ∀ d, R d.val (σ d) :=
  exists_measurable_section_of_countable_cover U hU hcover s hs
    (fun d x => R d.val x) hR

end PaperI
