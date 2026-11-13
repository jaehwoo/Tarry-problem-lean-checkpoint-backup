import PaperILean.GeometricSemialgebraicDimension
import PaperILean.PublishedFiniteConnectedCover
import Mathlib.Topology.Order.IntermediateValue

/-! Structural finite cell data from BPR 5.3/5.19. The dimension predicate is
the intrinsic definition on printed p.169, not finiteness or disconnectedness.
The published input supplies actual semialgebraic cube charts and a finite
partition. The point-cell and finite-cardinality consequences are local proofs.
No inhabitant of the published Prop contract is provided. -/

noncomputable section
namespace PaperI

structure SemialgebraicCellDecomposition {α : Type*} (S : Set (α → ℝ)) where
  count : ℕ
  cell : Fin count → Set (α → ℝ)
  dimension : Fin count → ℕ
  subset : ∀ i, cell i ⊆ S
  cover : ∀ x ∈ S, ∃ i, x ∈ cell i
  disjoint : Pairwise (fun i j => Disjoint (cell i) (cell j))
  cell_semialgebraic : ∀ i, HasPolynomialSignDescription (cell i)
  chart : ∀ i, openUnitCube (dimension i) ≃ₜ cell i
  chart_semialgebraic : ∀ i,
    HasPolynomialSignDescription (cubeMapGraph (fun x => (chart i x).val))

structure PublishedSemialgebraicCellDecomposition : Prop where
  cell_decomposition : ∀ {α : Type} [Finite α] (S : Set (α → ℝ)),
    HasPolynomialSignDescription S → Nonempty (SemialgebraicCellDecomposition S)

theorem SemialgebraicCellDecomposition.cubeInjection {α : Type*}
    {S : Set (α → ℝ)} (c : SemialgebraicCellDecomposition S) (i : Fin c.count) :
    HasSemialgebraicCubeInjection S (c.dimension i) := by
  refine ⟨fun x => (c.chart i x).val, ?_, ?_, c.chart_semialgebraic i⟩
  · intro x y h
    exact (c.chart i).injective (Subtype.ext h)
  · intro x
    exact c.subset i (c.chart i x).property

theorem SemialgebraicCellDecomposition.cell_dimension_zero {α : Type*}
    {S : Set (α → ℝ)} (c : SemialgebraicCellDecomposition S)
    (hdim : HasGeometricSemialgebraicDimension S 0) (i : Fin c.count) :
    c.dimension i = 0 :=
  cubeDimension_eq_zero_of_geometric_dimension_zero hdim (c.cubeInjection i)

theorem SemialgebraicCellDecomposition.point_cell_of_dimension_zero {α : Type*}
    {S : Set (α → ℝ)} (c : SemialgebraicCellDecomposition S)
    (hdim : HasGeometricSemialgebraicDimension S 0) (i : Fin c.count) :
    Subsingleton (c.cell i) := by
  have hz := c.cell_dimension_zero hdim i
  haveI : Subsingleton (openUnitCube (c.dimension i)) :=
    hz ▸ openUnitCube_zero_subsingleton
  exact (c.chart i).symm.injective.subsingleton

theorem SemialgebraicCellDecomposition.finite_of_dimension_zero {α : Type*}
    {S : Set (α → ℝ)} (c : SemialgebraicCellDecomposition S)
    (hdim : HasGeometricSemialgebraicDimension S 0) : Finite S := by
  letI : ∀ i, Subsingleton (c.cell i) := c.point_cell_of_dimension_zero hdim
  let f : (Σ i : Fin c.count, c.cell i) → S :=
    fun x => ⟨x.2.val, c.subset x.1 x.2.property⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨i, hi⟩ := c.cover x.val x.property
  exact ⟨⟨i, x.val, hi⟩, Subtype.ext rfl⟩

theorem published_finite_of_geometric_dimension_zero
    (hCell : PublishedSemialgebraicCellDecomposition)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S)
    (hdim : HasGeometricSemialgebraicDimension S 0) : Finite S := by
  obtain ⟨c⟩ := hCell.cell_decomposition S hS
  exact c.finite_of_dimension_zero hdim

theorem published_totallyDisconnected_of_geometric_dimension_zero
    (hCell : PublishedSemialgebraicCellDecomposition)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S)
    (hdim : HasGeometricSemialgebraicDimension S 0) : TotallyDisconnectedSpace S := by
  letI : Finite S := published_finite_of_geometric_dimension_zero hCell S hS hdim
  infer_instance

theorem published_finite_of_geometric_dimension_le_zero
    (hCell : PublishedSemialgebraicCellDecomposition)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S) {z : ℤ}
    (hdim : HasGeometricSemialgebraicDimension S z) (hz : z ≤ 0) : Finite S := by
  rcases geometric_dimension_le_zero_empty_or_zero hdim hz with rfl | hzero
  · infer_instance
  · exact published_finite_of_geometric_dimension_zero hCell S hS hzero

theorem published_totallyDisconnected_of_geometric_dimension_le_zero
    (hCell : PublishedSemialgebraicCellDecomposition)
    {α : Type} [Finite α] (S : Set (α → ℝ))
    (hS : HasPolynomialSignDescription S) {z : ℤ}
    (hdim : HasGeometricSemialgebraicDimension S z) (hz : z ≤ 0) : TotallyDisconnectedSpace S := by
  letI : Finite S := published_finite_of_geometric_dimension_le_zero hCell S hS hdim hz
  infer_instance

theorem openUnitCube_isPreconnected (d : ℕ) : IsPreconnected (openUnitCube d) := by
  have h : IsPreconnected (Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) :=
    isPreconnected_univ_pi (fun _ => isPreconnected_Ioo)
  simpa [openUnitCube, Set.pi] using h

/-- The stronger structural cell input supplies the earlier connected-cover
input, so downstream counts do not need a second accepted theorem parameter. -/
theorem PublishedSemialgebraicCellDecomposition.toFiniteConnectedCover
    (hCell : PublishedSemialgebraicCellDecomposition) : PublishedFiniteConnectedCover := by
  constructor
  intro α _ S hS
  obtain ⟨c⟩ := hCell.cell_decomposition S hS
  let f : ∀ i, openUnitCube (c.dimension i) → S :=
    fun i x => ⟨(c.chart i x).val, c.subset i (c.chart i x).property⟩
  refine ⟨c.count, fun i => Set.range (f i), ?_, ?_⟩
  · intro i
    letI : PreconnectedSpace (openUnitCube (c.dimension i)) :=
      Subtype.preconnectedSpace (openUnitCube_isPreconnected _)
    apply isPreconnected_range
    exact (continuous_subtype_val.comp (c.chart i).continuous).subtype_mk _
  · intro x
    obtain ⟨i, hi⟩ := c.cover x.val x.property
    refine ⟨i, (c.chart i).symm ⟨x.val, hi⟩, ?_⟩
    apply Subtype.ext
    change ((c.chart i) ((c.chart i).symm ⟨x.val, hi⟩)).val = x.val
    rw [(c.chart i).apply_symm_apply]

end PaperI
