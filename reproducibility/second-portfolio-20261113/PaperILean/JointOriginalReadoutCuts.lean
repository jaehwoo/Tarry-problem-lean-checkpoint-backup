import PaperILean.JointOrderedCuts
import PaperILean.SamePathPlanarGraphSubdivision
import PaperILean.JointUnitPathMeasurability

/-! Joint original analytic/sign cuts for the four planar readouts on the
SAME supplied jointly semialgebraic path. The active count and all time cuts
are Borel before any arbitrary Borel parameter pullback. No jointly selected
graph direction or prepared interval is asserted by these statements. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem JointOriginalScalarCutFamily.on_subinterval {α : Type*}
    {G : Set ((α ⊕ Fin 2) → ℝ)} {C : Set ((α ⊕ Unit) → ℝ)} {K : ℕ}
    (h : JointOriginalScalarCutFamily G C K) (p : α → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ t ∈ Icc (0:ℝ) 1, ∀ y, Sum.elim p ![t,y] ∈ G ↔ y=f t)
    {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) (huv : u<v)
    (hgap : ∀ c ∈ scalarProjectionFiber C p, c ∉ Ioo u v) :
    AnalyticOnNhd ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  classical
  have hp := h p
  let F := hp.1.toFinset
  obtain ⟨l,hl,r,hr,hlu,hvr,hlr,hno⟩ := exists_consecutive_cuts_containing F
    (hp.1.mem_toFinset.mpr hp.2.2.1) (hp.1.mem_toFinset.mpr hp.2.2.2.1)
    hu.1 hv.2 huv (fun c hc => hgap c (hp.1.mem_toFinset.mp hc))
  have hloc := hp.2.2.2.2.2 f hrep l (hp.1.mem_toFinset.mp hl)
    r (hp.1.mem_toFinset.mp hr) hlr (fun c hc => hno c (hp.1.mem_toFinset.mpr hc))
  exact ⟨hloc.1.mono (Ioo_subset_Ioo hlu hvr),derivativeSignOn_mono hloc.2 (Ioo_subset_Ioo hlu hvr)⟩

/-- The common refinement is itself a fixed joint semialgebraic relation.
The assertion includes empty readout families; endpoints are still retained. -/
theorem published_joint_original_common_cut_family
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α ι : Type} [Finite α] [Fintype ι]
    (G : ι → Set ((α ⊕ Fin 2) → ℝ))
    (hG : ∀ i, (univ : Set ℝ).Definable Language.ring (G i)) :
    ∃ (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ), HasPolynomialSignDescription C ∧
      (∀ p, (scalarProjectionFiber C p).Finite ∧ Nat.card (scalarProjectionFiber C p) ≤ K ∧
        0 ∈ scalarProjectionFiber C p ∧ 1 ∈ scalarProjectionFiber C p ∧
        scalarProjectionFiber C p ⊆ Icc (0:ℝ) 1) ∧
      ∀ i, JointOriginalScalarCutFamily (G i) C K := by
  classical
  choose B H hB hcuts using
    (fun i => published_joint_original_scalar_cut_family hCell hHardt hQE hPiece (G i) (hG i))
  let C := jointUnitCutRelation B
  have hC : HasPolynomialSignDescription C := hQE.finite_sign_description _
    (jointUnitCutRelation_definable (fun i => hasPolynomialSignDescription_definable (hB i)))
  obtain ⟨K,hK⟩ := published_scalar_finite_fiber_card_bound hCell hHardt hQE C hC
  have hbase (p : α → ℝ) : (scalarProjectionFiber C p).Finite ∧
      Nat.card (scalarProjectionFiber C p) ≤ K ∧
      0 ∈ scalarProjectionFiber C p ∧ 1 ∈ scalarProjectionFiber C p ∧
      scalarProjectionFiber C p ⊆ Icc (0:ℝ) 1 := by
    have hf := jointUnitCutRelation_finite B p (fun i => (hcuts i p).1)
    have he := jointUnitCutRelation_endpoints B p
    exact ⟨hf,hK p hf,he.1,he.2,jointUnitCutRelation_subset B p⟩
  refine ⟨C,K,hC,hbase,?_⟩
  intro i p
  have hb := hbase p
  refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2,?_⟩
  intro f hrep u hu v hv huv hgap
  apply (hcuts i).on_subinterval p f hrep (hb.2.2.2.2 hu) (hb.2.2.2.2 hv) huv
  intro c hc
  apply hgap c
  exact ⟨(hcuts i p).2.2.2.2.1 hc,Or.inr (Or.inr ⟨i,hc⟩)⟩

def jointPlanarReadoutGraph {α : Type*} (P : Set (α → ℝ))
    (g : (α → ℝ) → ℝ → Fin 2 → ℝ) (i : Fin 4) : Set ((α ⊕ Fin 2) → ℝ) :=
  scalarRelationCompositionFamily (jointUnitPathGraph P g)
    {v : (α ⊕ (Fin 2 ⊕ Unit)) → ℝ | v ∘ Sum.inr ∈ scalarFunctionGraph univ (planarReadout i)}

theorem jointPlanarReadoutGraph_definable {α : Type} [Finite α]
    {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) (i : Fin 4) :
    (univ : Set ℝ).Definable Language.ring (jointPlanarReadoutGraph P g i) := by
  obtain ⟨A,_,_,hA⟩ := planarReadout_global_graph_format i
  exact scalarRelationCompositionFamily_definable (hasPolynomialSignDescription_definable hg)
    ((hasPolynomialSignDescription_definable ⟨A,hA⟩).preimage_comp Sum.inr)

theorem jointPlanarReadoutGraph_realize {α : Type*} (P : Set (α → ℝ))
    (g : (α → ℝ) → ℝ → Fin 2 → ℝ) (i : Fin 4) {p : α → ℝ} (hp : p∈P)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (y : ℝ) :
    Sum.elim p ![t,y] ∈ jointPlanarReadoutGraph P g i ↔ y=planarReadout i (g p t) := by
  change (∃ x : Fin 2 → ℝ, (p∈P ∧ t∈Icc (0:ℝ) 1 ∧ x=g p t) ∧
    (x∈univ ∧ y=planarReadout i x)) ↔ _
  simp [hp,ht]

def OriginalPlanarReadoutPartition (g : ℝ → Fin 2 → ℝ) (K n : ℕ) (t : ℕ → ℝ) : Prop :=
  0<n ∧ n≤K ∧ t 0=0 ∧ t n=1 ∧ MonotoneOn t (Icc 0 n) ∧
    (∀ j≥n, t j=1) ∧
    ∀ j<n, t j ∈ Icc (0:ℝ) 1 ∧ t (j+1) ∈ Icc (0:ℝ) 1 ∧ t j<t (j+1) ∧
      ∀ i : Fin 4, AnalyticOnNhd ℝ (fun r => planarReadout i (g r)) (Ioo (t j) (t (j+1))) ∧
        DerivativeSignOn (fun r => planarReadout i (g r)) (Ioo (t j) (t (j+1)))

theorem OriginalPlanarReadoutPartition.graph_arcs {g : ℝ → Fin 2 → ℝ} {K n : ℕ} {t : ℕ → ℝ}
    (h : OriginalPlanarReadoutPartition g K n t) (hc : ContinuousOn g (Icc (0:ℝ) 1)) :
    ∀ j<n, OriginalPlanarGraphArc g (t j) (t (j+1)) := by
  intro j hj
  obtain ⟨hu,hv,huv,hread⟩ := h.2.2.2.2.2.2 j hj
  apply originalPlanarGraphArc_of_sum_sub_signs huv.le
  · intro k
    exact ((continuous_apply k).comp_continuousOn hc).mono (Icc_subset_Icc hu.1 hv.2)
  · intro k
    fin_cases k
    · simpa [planarReadout,planarReadoutPolynomial] using (hread 0).1.differentiableOn
    · simpa [planarReadout,planarReadoutPolynomial] using (hread 1).1.differentiableOn
  · simpa [planarReadout,planarReadoutPolynomial] using (hread 2).2
  · simpa [planarReadout,planarReadoutPolynomial] using (hread 3).2

/-- A fixed supplied joint graph gives one bound and Borel cuts before every
parameter. Off-domain path values are irrelevant. -/
theorem published_joint_original_planar_readout_partition
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (P : Set (α → ℝ)) (g : (α → ℝ) → ℝ → Fin 2 → ℝ)
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    ∃ (K : ℕ) (n : (α → ℝ) → ℕ) (t : (α → ℝ) → ℕ → ℝ),
      Measurable n ∧ (∀ j, Measurable (fun p => t p j)) ∧
      ∀ p∈P, OriginalPlanarReadoutPartition (g p) K (n p) (t p) := by
  obtain ⟨C,K,hC,hbase,hcuts⟩ := published_joint_original_common_cut_family
    hCell hHardt hQE hPiece (jointPlanarReadoutGraph P g) (jointPlanarReadoutGraph_definable hg)
  obtain ⟨n,t,hn,ht,hord⟩ := published_joint_ordered_unit_cuts hCAD hQE hHardt C hC K
    (fun p => (hbase p).1) (fun p => (hbase p).2.1.trans (Nat.le_succ K))
    (fun p => (hbase p).2.2.1) (fun p => (hbase p).2.2.2.1) (fun p => (hbase p).2.2.2.2)
  refine ⟨K,n,t,hn,ht,?_⟩
  intro p hp
  obtain ⟨hnp,hnK,ht0,htn,hm,htail,hgap⟩ := hord p
  refine ⟨hnp,hnK,ht0,htn,hm,htail,?_⟩
  intro j hj
  obtain ⟨hu,hv,huv,hno⟩ := hgap j hj
  refine ⟨(hbase p).2.2.2.2 hu,(hbase p).2.2.2.2 hv,huv,?_⟩
  intro i
  exact (hcuts i p).2.2.2.2.2 (fun r => planarReadout i (g p r))
    (fun r hr y => jointPlanarReadoutGraph_realize P g i hp hr y)
    (t p j) hu (t p (j+1)) hv huv hno

/-- Arbitrary Borel substitution is performed only AFTER joint construction.
This claims Borel measurability, not semialgebraicity of the substituted family. -/
theorem published_joint_original_planar_readout_partition_comp
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (P : Set (α → ℝ)) (g : (α → ℝ) → ℝ → Fin 2 → ℝ)
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    ∃ K : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (q : Ω → P), Measurable q →
      ∃ (n : Ω → ℕ) (t : Ω → ℕ → ℝ), Measurable n ∧
        (∀ j, Measurable (fun ω => t ω j)) ∧
        ∀ ω, OriginalPlanarReadoutPartition (g (q ω).val) K (n ω) (t ω) := by
  obtain ⟨K,n,t,hn,ht,hpart⟩ := published_joint_original_planar_readout_partition
    hCAD hCell hHardt hQE hPiece P g hg
  refine ⟨K,?_⟩
  intro Ω inst q hq
  have hqv := measurable_subtype_coe.comp hq
  exact ⟨fun ω => n (q ω).val,fun ω => t (q ω).val,hn.comp hqv,
    fun j => (ht j).comp hqv,fun ω => hpart (q ω).val (q ω).property⟩

end PaperI
