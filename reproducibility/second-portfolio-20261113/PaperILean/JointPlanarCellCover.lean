import PaperILean.PlanarCylindricalCells
import PaperILean.CylindricalFiniteGraphCover

/-! A finite jointly semialgebraic cover by actual planar cells in each fiber.
All parameters precede the two planar coordinates in the CAD call. No new
published contract, boundedness assumption or dimension assumption is used. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure JointPlanarCellCover {ρ : Type} (S : Set ((ρ ⊕ Fin 2) → ℝ)) where
  count : ℕ
  cell : Fin count → Set ((ρ ⊕ Fin 2) → ℝ)
  cell_sign : ∀ i, HasPolynomialSignDescription (cell i)
  cell_subset : ∀ i, cell i ⊆ S
  cover : ∀ v, v ∈ S ↔ ∃ i, v ∈ cell i
  fiber_cell : ∀ i p, projectionFiber (cell i) p = ∅ ∨
    IsPlanarCylindricalCell (projectionFiber (cell i) p)

theorem published_joint_planar_cell_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (S : Set ((ρ ⊕ Fin 2) → ℝ))
    (hS : HasPolynomialSignDescription S) : Nonempty (JointPlanarCellCover S) := by
  classical
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE 2 univ
    (cadUnpackedRelation 2 S) (hQE.finite_sign_description _ definable_univ)
    (hQE.finite_sign_description _ (cadUnpackedRelation_definable 2
      (hasPolynomialSignDescription_definable hS)))
  let e : Fin (Fintype.card d.slicedLeaf) ≃ d.slicedLeaf := (Fintype.equivFin _).symm
  have hsub (i : Fin (Fintype.card d.slicedLeaf)) : d.slicedFiberCell (e i) ⊆ S := by
    intro v hv
    have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
      funext i; cases i <;> rfl
    have hh : (v ∘ Sum.inr) ∈ projectionFiber (d.slicedFiberCell (e i)) (v ∘ Sum.inl) := by
      simpa only [projectionFiber,mem_setOf_eq,he] using hv
    have h := d.slicedFiberCell_subset (e i) (v ∘ Sum.inl) hh
    simpa only [cadPackedRelation_unpacked,projectionFiber,mem_setOf_eq,he] using h
  refine ⟨{ count := Fintype.card d.slicedLeaf
            cell := fun i => d.slicedFiberCell (e i)
            cell_sign := fun i => hQE.finite_sign_description _ (d.slicedFiberCell_definable (e i))
            cell_subset := hsub
            fiber_cell := fun i p => d.planar_slicedFiberCell_cases (e i) p
            cover := ?_ }⟩
  intro v
  constructor
  · intro hv
    have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
      funext i; cases i <;> rfl
    obtain ⟨j,hj⟩ := d.slicedFiberCell_cover (mem_univ (v ∘ Sum.inl))
      (x := v ∘ Sum.inr) (by simpa only [cadPackedRelation_unpacked,projectionFiber,mem_setOf_eq,he] using hv)
    exact ⟨e.symm j,by simpa only [projectionFiber,mem_setOf_eq,he,e.apply_symm_apply] using hj⟩
  · rintro ⟨i,hi⟩
    exact hsub i hi

theorem JointPlanarCellCover.fiber_cover {ρ : Type} {S : Set ((ρ ⊕ Fin 2) → ℝ)}
    (C : JointPlanarCellCover S) (p : ρ → ℝ) :
    (⋃ i, projectionFiber (C.cell i) p) = projectionFiber S p := by
  ext x
  simp only [mem_iUnion,projectionFiber,mem_setOf_eq]
  exact (C.cover _).symm

theorem JointPlanarCellCover.common_format {ρ : Type} {S : Set ((ρ ⊕ Fin 2) → ℝ)}
    (C : JointPlanarCellCover S) :
    ∃ s d : ℕ, ∀ i, ∃ A : Finset (MvPolynomial (ρ ⊕ Fin 2) ℝ),
      A.card ≤ s ∧ (∀ q ∈ A, q.totalDegree ≤ d) ∧ PolynomialSignDetermined A (C.cell i) :=
  finite_sign_descriptions_common_format _ C.cell_sign

end PaperI
