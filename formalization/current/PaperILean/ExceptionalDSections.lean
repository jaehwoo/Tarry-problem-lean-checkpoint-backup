import PaperILean.FiniteAxisCuts

/-! I3228[333,436): a uniform finite exceptional-parameter list and actual
whole-axis section refinement. Previously constructed component sections,
their component bijections and their original coordinates are retained. -/
noncomputable section
namespace PaperI.ExceptionalDSections
open Set ActualDSections
open scoped BigOperators

def parameterCell (C L : Finset ℝ) : Set (Fin 1 → ℝ) :=
  {p | p 0 ∈ axisCutCell C L}

theorem fin1_constant (p : Fin 1 → ℝ) : (fun _ : Fin 1 => p 0) = p := by
  funext i
  rw [Fin.eq_zero i]

def restrictSection {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) :
    parameterCell C L → Fin 6 → ℝ :=
  fun p => F.sectionFn i j ⟨p.val,hU p.property⟩

theorem restrictSection_continuous {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) :
    Continuous (restrictSection F i j C L hU) :=
  (F.section_continuous i j).comp
    (continuous_subtype_val.subtype_mk (fun p => hU p.property))

theorem restrictSection_graph {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) :
    componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU) =
      componentSectionGraph (F.piece i) (F.sectionFn i j) ∩
        {z | z (Sum.inl 0) ∈ axisCutCell C L} := by
  ext z
  constructor
  · rintro ⟨hp,hg⟩
    exact ⟨⟨hU hp,hg⟩,hp⟩
  · rintro ⟨⟨hp,hg⟩,hu⟩
    exact ⟨hu,hg⟩

theorem restrictSection_region {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (i : Fin F.n) (j : Fin (F.m i))
    (C L : Finset ℝ) (hU : parameterCell C L ⊆ F.piece i) :
    componentSectionRegion (actualDRelation E) (parameterCell C L)
        (restrictSection F i j C L hU) =
      componentSectionRegion (actualDRelation E) (F.piece i) (F.sectionFn i j) ∩
        {z | z (Sum.inl 0) ∈ axisCutCell C L} := by
  ext z
  constructor
  · rintro ⟨hp,hg⟩
    exact ⟨⟨hU hp,hg⟩,hp⟩
  · rintro ⟨⟨hp,hg⟩,hu⟩
    exact ⟨hu,hg⟩

theorem cell_inside_or_empty {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (C L : Finset ℝ)
    (hfront : ∀ i, frontier {t : ℝ | (fun _ : Fin 1 => t) ∈ F.piece i} ⊆ C) :
    (∀ t ∈ axisCutCell C L,
      projectionFiber (actualDRelation E) (fun _ => t) = ∅) ∨
    ∃ i : Fin F.n, parameterCell C L ⊆ F.piece i := by
  classical
  by_cases h : ∃ t ∈ axisCutCell C L,
      (fun _ : Fin 1 => t) ∈ projectionDomain (actualDRelation E)
  · obtain ⟨t,ht,hdom⟩ := h
    obtain ⟨i,hi⟩ := F.cover _ hdom
    have hsub : axisCutCell C L ⊆ {t : ℝ | (fun _ : Fin 1 => t) ∈ F.piece i} :=
      preconnected_subset_of_avoids_frontier_of_mem (axisCutCell_preconnected C L)
        (fun x hx hfx => axisCutCell_avoids C L hx (hfront i hfx)) ⟨t,ht,hi⟩
    refine Or.inr ⟨i,?_⟩
    intro p hp
    have hi' := hsub hp
    simpa only [mem_setOf_eq, fin1_constant] using hi'
  · left
    intro t ht
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro g hg
    exact h ⟨t,ht,⟨g,hg⟩⟩

/-- The actual finite exceptional list, with coefficient-uniform bounds and
continuous bounded-format component sections on every nonexceptional cell.
The singleton values in C are retained, and the cell cover includes rays. -/
theorem actual_d_exceptional_list
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ N sOut dOut K : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∃ (F : ComponentSectionAtlas (actualDRelation E)) (C : Finset ℝ),
        F.Bounded N sOut dOut ∧ Nonempty (FixedOrderAssignment F sOut dOut) ∧
        C.card ≤ K ∧ C.powerset.card ≤ 2^K ∧
        (∀ t : ℝ, t ∈ C ∨ ∃ L ∈ C.powerset, t ∈ axisCutCell C L) ∧
        (∀ L ∈ C.powerset, ∀ M ∈ C.powerset, L ≠ M →
          Disjoint (axisCutCell C L) (axisCutCell C M)) ∧
        (∀ L ∈ C.powerset, IsOpen (axisCutCell C L) ∧
          IsPreconnected (axisCutCell C L) ∧
          (∀ t ∈ axisCutCell C L, t ∉ C) ∧
          ((∀ t ∈ axisCutCell C L,
              projectionFiber (actualDRelation E) (fun _ => t) = ∅) ∨
            ∃ (i : Fin F.n) (hU : parameterCell C L ⊆ F.piece i),
              (∀ j : Fin (F.m i),
                Continuous (restrictSection F i j C L hU) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionGraph (parameterCell C L) (restrictSection F i j C L hU)) ∧
                HasBoundedSignFormat (sOut+K) (max dOut 1)
                  (componentSectionRegion (actualDRelation E) (parameterCell C L)
                    (restrictSection F i j C L hU))) ∧
              (∀ j (p : parameterCell C L),
                restrictSection F i j C L hU p ∈ E ∧
                (restrictSection F i j C L hU p) 3 = p.val 0) ∧
              ∀ p : parameterCell C L, Function.Bijective
                (fun j => ConnectedComponents.mk
                  (⟨restrictSection F i j C L hU p,
                    F.section_mem i j ⟨p.val,hU p.property⟩⟩ :
                    projectionFiber (actualDRelation E) p.val)))) := by
  classical
  obtain ⟨N,sOut,dOut,hAtlas⟩ := actual_d_sections_stage hCell hHardt hQE s D
  obtain ⟨K0,hK0⟩ := bounded_fin1_scalar_frontier hCell hHardt hQE sOut dOut
  refine ⟨N,sOut,dOut,N*K0,?_⟩
  intro A E hc hd hE
  obtain ⟨F,hF,hcount,hactual,hwhole,hassign,hfiber⟩ := hAtlas A E hc hd hE
  let bad : Fin F.n → Set ℝ := fun i => frontier {t | (fun _ : Fin 1 => t) ∈ F.piece i}
  have hfin : ∀ i, (bad i).Finite := fun i => (hK0 (F.piece i) (hF.piece_format i)).1
  have hcard : ∀ i, Nat.card (bad i) ≤ K0 := fun i => (hK0 (F.piece i) (hF.piece_format i)).2
  let C : Finset ℝ := Finset.univ.biUnion (fun i => (hfin i).toFinset)
  have hC : C.card ≤ N*K0 := by
    calc
      C.card ≤ ∑ i : Fin F.n, (hfin i).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin F.n, K0 := Finset.sum_le_sum (fun i _ => by
        simpa only [Nat.card_eq_card_finite_toFinset (hfin i)] using hcard i)
      _ = F.n*K0 := by simp
      _ ≤ N*K0 := Nat.mul_le_mul_right K0 hF.pieces_le
  have hfront : ∀ i, bad i ⊆ (C : Set ℝ) := by
    intro i t ht
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,(hfin i).mem_toFinset.mpr ht⟩
  refine ⟨F,C,hF,hassign,hC,?_,?_,?_,?_⟩
  · rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide) hC
  · intro t
    by_cases ht : t ∈ C
    · exact Or.inl ht
    · exact Or.inr (axisCutCell_cover C ht)
  · intro L hL M hM hne
    exact axisCutCell_disjoint C L M (Finset.mem_powerset.mp hL) (Finset.mem_powerset.mp hM) hne
  · intro L hL
    refine ⟨axisCutCell_open C L,axisCutCell_preconnected C L,
      fun t ht => axisCutCell_avoids C L ht,?_⟩
    rcases cell_inside_or_empty F C L hfront with he | ⟨i,hU⟩
    · exact Or.inl he
    · right
      refine ⟨i,hU,?_,?_,?_⟩
      · intro j
        refine ⟨restrictSection_continuous F i j C L hU,?_,?_⟩
        · rw [restrictSection_graph]
          exact ((hF.graph_format i j).inter (axisCutCell_format (Sum.inl 0) C L)).mono
            (Nat.add_le_add_left hC sOut) le_rfl
        · rw [restrictSection_region]
          exact ((hF.region_format i j).inter (axisCutCell_format (Sum.inl 0) C L)).mono
            (Nat.add_le_add_left hC sOut) le_rfl
      · intro j p
        exact hactual i j ⟨p.val,hU p.property⟩
      · intro p
        exact F.component_bijective i ⟨p.val,hU p.property⟩

end PaperI.ExceptionalDSections
