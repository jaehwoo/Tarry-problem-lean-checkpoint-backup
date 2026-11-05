import PaperILean.CylindricalSlicedAttachments
import PaperILean.JointCellChainSelectionFormat

/-! Packaging of actual joint path graphs and their pointwise verified unit
paths. The structure is local data, not a new published assumption. Finite
composition preserves the same function; gluing requires definable regions.
Prospective obstruction record: checkpoint_121_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure JointSemialgebraicPath {ρ κ : Type} (P : Set (ρ → ℝ))
    (S : Set ((ρ ⊕ κ) → ℝ)) (x y : (ρ → ℝ) → κ → ℝ) where
  toFun : (ρ → ℝ) → ℝ → κ → ℝ
  graph : HasPolynomialSignDescription (jointUnitPathGraph P toFun)
  path : ∀ p ∈ P, ∃ γ : SemialgebraicUnitPath (projectionFiber S p) (x p) (y p),
    γ.toFun = toFun p

def JointSemialgebraicPath.trans {ρ κ : Type} {P : Set (ρ → ℝ)}
    {S : Set ((ρ ⊕ κ) → ℝ)} {x y z : (ρ → ℝ) → κ → ℝ}
    (g : JointSemialgebraicPath P S x y) (h : JointSemialgebraicPath P S y z) :
    JointSemialgebraicPath P S x z where
  toFun p := unitPathConcat (g.toFun p) (h.toFun p)
  graph := jointUnitPathGraph_concat_semialgebraic g.graph h.graph
  path := by
    intro p hp
    obtain ⟨γ,hγ⟩ := g.path p hp
    obtain ⟨η,hη⟩ := h.path p hp
    exact ⟨γ.trans η,by simp only [SemialgebraicUnitPath.trans_toFun,hγ,hη]⟩

def JointSemialgebraicPath.reverse {ρ κ : Type} {P : Set (ρ → ℝ)}
    {S : Set ((ρ ⊕ κ) → ℝ)} {x y : (ρ → ℝ) → κ → ℝ}
    (g : JointSemialgebraicPath P S x y) : JointSemialgebraicPath P S y x where
  toFun p := unitPathReverse (g.toFun p)
  graph := jointUnitPathGraph_reverse_semialgebraic g.graph
  path := by
    intro p hp
    obtain ⟨γ,hγ⟩ := g.path p hp
    exact ⟨γ.reverse,by simp only [SemialgebraicUnitPath.reverse_toFun,hγ]⟩

/-- Append a finite chain to an actual starting path. In the zero-edge case
the starting path is retained, not replaced by a constant path. -/
def JointSemialgebraicPath.chain {ρ κ : Type} {P : Set (ρ → ℝ)}
    {S : Set ((ρ ⊕ κ) → ℝ)} {x : (ρ → ℝ) → κ → ℝ} :
    (m : ℕ) → (z : Fin (m+1) → (ρ → ℝ) → κ → ℝ) →
    JointSemialgebraicPath P S x (z 0) →
    (∀ i : Fin m, JointSemialgebraicPath P S (z i.castSucc) (z i.succ)) →
    JointSemialgebraicPath P S x (z (Fin.last m))
  | 0, _, start, _ => start
  | m+1, z, start, edges =>
    JointSemialgebraicPath.chain m (fun i => z i.succ) (start.trans (edges 0))
      (fun i => edges i.succ)

theorem JointSemialgebraicPath.uniform_format {ρ κ : Type}
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ κ) → ℝ)} {x y : (ρ → ℝ) → κ → ℝ}
    (g : JointSemialgebraicPath P S x y) :
    ∃ s d : ℕ, ∀ p ∈ P,
      ∃ γ : SemialgebraicUnitPath (projectionFiber S p) (x p) (y p),
        γ.toFun = g.toFun p ∧ ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ),
          A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨s,d,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format P g.toFun g.graph
  refine ⟨s,d,?_⟩
  intro p hp
  obtain ⟨γ,hγ⟩ := g.path p hp
  obtain ⟨A,hs,hd,hA⟩ := hfmt p hp
  exact ⟨γ,hγ,A,hs,hd,by simpa only [hγ] using hA⟩

def finiteSelectorRegion {ρ ι : Type} (P : Set (ρ → ℝ)) (pick : P → ι) (i : ι) :
    Set (ρ → ℝ) := {p | ∃ hp : p ∈ P, pick ⟨p,hp⟩ = i}

theorem finiteSelectorRegion_subset {ρ ι : Type} (P : Set (ρ → ℝ)) (pick : P → ι) (i : ι) :
    finiteSelectorRegion P pick i ⊆ P := fun _ h => h.choose

theorem finiteSelectorRegion_cover {ρ ι : Type} (P : Set (ρ → ℝ)) (pick : P → ι) :
    ∀ p ∈ P, ∃ i, p ∈ finiteSelectorRegion P pick i :=
  fun p hp => ⟨pick ⟨p,hp⟩,hp,rfl⟩

theorem finiteSelectorRegion_disjoint {ρ ι : Type} (P : Set (ρ → ℝ)) (pick : P → ι) :
    Pairwise (fun i j => Disjoint (finiteSelectorRegion P pick i) (finiteSelectorRegion P pick j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro p ⟨hp,hi⟩ ⟨_,hj⟩
  exact hij (hi.symm.trans hj)

theorem cadPartitionGlue_unitPath_graph {ρ κ ι : Type} (P : Set (ρ → ℝ))
    (U : ι → Set (ρ → ℝ)) (hsub : ∀ i, U i ⊆ P)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (g : ι → (ρ → ℝ) → ℝ → κ → ℝ) :
    jointUnitPathGraph P (cadPartitionGlue P U hcover g) = ⋃ i, jointUnitPathGraph (U i) (g i) := by
  ext v
  simp only [jointUnitPathGraph,mem_setOf_eq,mem_iUnion]
  constructor
  · rintro ⟨hp,hv⟩
    let i := cadPartitionIndex P U hcover ⟨v ∘ Sum.inl,hp⟩
    have hi := cadPartitionIndex_mem P U hcover ⟨v ∘ Sum.inl,hp⟩
    exact ⟨i,hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis g hi] using hv⟩
  · rintro ⟨i,hi,hv⟩
    exact ⟨hsub i hi,by simpa only [cadPartitionGlue_on_cell P U hsub hcover hdis g hi] using hv⟩

def JointSemialgebraicPath.glue (hQE : PublishedRealSemialgebraicity)
    {ρ κ ι : Type} [Finite ρ] [Finite κ] [Fintype ι]
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ κ) → ℝ)) (x y : (ρ → ℝ) → κ → ℝ)
    (pick : P → ι)
    (g : ∀ i, JointSemialgebraicPath (finiteSelectorRegion P pick i) S x y) :
    JointSemialgebraicPath P S x y where
  toFun := cadPartitionGlue P (finiteSelectorRegion P pick) (finiteSelectorRegion_cover P pick)
    (fun i => (g i).toFun)
  graph := by
    apply hQE.finite_sign_description
    rw [cadPartitionGlue_unitPath_graph P _ (finiteSelectorRegion_subset P pick)
      (finiteSelectorRegion_cover P pick) (finiteSelectorRegion_disjoint P pick)]
    exact cad_definable_finite_iUnion (fun i => hasPolynomialSignDescription_definable (g i).graph)
  path := by
    intro p hp
    obtain ⟨i,hi⟩ := finiteSelectorRegion_cover P pick p hp
    obtain ⟨γ,hγ⟩ := (g i).path p hi
    refine ⟨γ,?_⟩
    rw [cadPartitionGlue_on_cell P _ (finiteSelectorRegion_subset P pick)
      (finiteSelectorRegion_cover P pick) (finiteSelectorRegion_disjoint P pick) _ hi]
    exact hγ

end PaperI
