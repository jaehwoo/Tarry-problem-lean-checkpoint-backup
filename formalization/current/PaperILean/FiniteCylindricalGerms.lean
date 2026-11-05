import PaperILean.CylindricalGermAttachment

/-! Finite gluing on a disjoint parameter partition. The index is constant
as a choice on each whole base cell, not chosen independently for each time.
Only continuity of each time-fiber is asserted. Empty P needs no index value. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def cadPartitionIndex {ρ ι : Type} (P : Set (ρ → ℝ)) (U : ι → Set (ρ → ℝ))
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i) (p : P) : ι :=
  (hcover p.val p.property).choose

theorem cadPartitionIndex_mem {ρ ι : Type} (P : Set (ρ → ℝ)) (U : ι → Set (ρ → ℝ))
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i) (p : P) :
    p.val ∈ U (cadPartitionIndex P U hcover p) :=
  (hcover p.val p.property).choose_spec

theorem cadPartitionIndex_eq {ρ ι : Type} (P : Set (ρ → ℝ)) (U : ι → Set (ρ → ℝ))
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (p : P) (i : ι) (hi : p.val ∈ U i) : cadPartitionIndex P U hcover p = i := by
  by_contra h
  exact Set.disjoint_left.mp (hdis h) (cadPartitionIndex_mem P U hcover p) hi

def cadPartitionGlue {ρ ι X : Type} [Zero X] (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (f : ι → (ρ → ℝ) → X) (p : ρ → ℝ) : X :=
  if hp : p ∈ P then f (cadPartitionIndex P U hcover ⟨p,hp⟩) p else 0

theorem cadPartitionGlue_on_cell {ρ ι X : Type} [Zero X] (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (f : ι → (ρ → ℝ) → X) {p : ρ → ℝ} {i : ι} (hi : p ∈ U i) :
    cadPartitionGlue P U hcover f p = f i p := by
  rw [cadPartitionGlue,dif_pos (hsub i hi),cadPartitionIndex_eq P U hcover hdis _ i hi]

theorem cadPartitionGlue_scalar_graph {ρ ι : Type} (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (β : ι → (ρ → ℝ) → ℝ) :
    selectedFunctionGraph P (fun p (_ : Unit) => cadPartitionGlue P U hcover β p) =
      ⋃ i, selectedFunctionGraph (U i) (fun p (_ : Unit) => β i p) := by
  ext v
  simp only [selectedFunctionGraph,mem_setOf_eq,mem_iUnion]
  constructor
  · rintro ⟨hp,hv⟩
    let i := cadPartitionIndex P U hcover ⟨fun r => v (Sum.inl r),hp⟩
    have hi := cadPartitionIndex_mem P U hcover ⟨fun r => v (Sum.inl r),hp⟩
    refine ⟨i,hi,?_⟩
    simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis β hi] using hv
  · rintro ⟨i,hi,hv⟩
    exact ⟨hsub i hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis β hi] using hv⟩

theorem cadPartitionGlue_germ_graph {ρ κ ι : Type} (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (β : ι → (ρ → ℝ) → ℝ) (g : ι → (ρ → ℝ) → ℝ → κ → ℝ) :
    jointCurveGermGraph P (cadPartitionGlue P U hcover β) (cadPartitionGlue P U hcover g) =
      ⋃ i, jointCurveGermGraph (U i) (β i) (g i) := by
  ext v
  simp only [jointCurveGermGraph,mem_setOf_eq,mem_iUnion]
  constructor
  · rintro ⟨hp,hv⟩
    let i := cadPartitionIndex P U hcover ⟨v ∘ Sum.inl,hp⟩
    have hi := cadPartitionIndex_mem P U hcover ⟨v ∘ Sum.inl,hp⟩
    refine ⟨i,hi,?_⟩
    simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis β hi,
      cadPartitionGlue_on_cell P U hsub hcover hdis g hi] using hv
  · rintro ⟨i,hi,hv⟩
    exact ⟨hsub i hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis β hi,
      cadPartitionGlue_on_cell P U hsub hcover hdis g hi] using hv⟩

theorem cad_definable_finite_iUnion {α ι : Type} [Fintype ι]
    {S : ι → Set (α → ℝ)}
    (hS : ∀ i, (univ : Set ℝ).Definable Language.ring (S i)) :
    (univ : Set ℝ).Definable Language.ring (⋃ i, S i) := by
  simpa using Set.definable_finset_biUnion hS Finset.univ

theorem finite_cylindrical_germs_glue {ρ κ ι : Type} [Fintype ι]
    (P : Set (ρ → ℝ)) (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (β : ι → (ρ → ℝ) → ℝ) (g : ι → (ρ → ℝ) → ℝ → κ → ℝ)
    (hβ : ∀ i, (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph (U i) (fun p (_ : Unit) => β i p)))
    (hg : ∀ i, (univ : Set ℝ).Definable Language.ring (jointCurveGermGraph (U i) (β i) (g i)))
    (hlocal : ∀ i, ∀ p ∈ U i, 0 < β i p ∧ g i p 0 = a p ∧
      ContinuousOn (g i p) (Ico (0 : ℝ) (β i p)) ∧
      MapsTo (g i p) (Ioo (0 : ℝ) (β i p)) (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → κ → ℝ),
      (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      (univ : Set ℝ).Definable Language.ring (jointCurveGermGraph P ε γ) ∧
      ∀ p ∈ P, 0 < ε p ∧ γ p 0 = a p ∧ ContinuousOn (γ p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (γ p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p) := by
  refine ⟨cadPartitionGlue P U hcover β,cadPartitionGlue P U hcover g,?_,?_,?_⟩
  · rw [cadPartitionGlue_scalar_graph P U hsub hcover hdis]
    exact cad_definable_finite_iUnion hβ
  · rw [cadPartitionGlue_germ_graph P U hsub hcover hdis]
    exact cad_definable_finite_iUnion hg
  · intro p hp
    let i := cadPartitionIndex P U hcover ⟨p,hp⟩
    have hi := cadPartitionIndex_mem P U hcover ⟨p,hp⟩
    simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis β hi,
      cadPartitionGlue_on_cell P U hsub hcover hdis g hi] using hlocal i p hi

end PaperI
