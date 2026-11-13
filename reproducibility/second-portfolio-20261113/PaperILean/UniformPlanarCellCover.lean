import PaperILean.PlanarSlicedCellGeometry
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! I1261: actual bounded thin planar fibers have a uniformly finite cover by
points and coordinate graphs, with uniform image sign format. All bounds for a
fixed joint family precede its parameter. Universal coefficient families then
make the bounds depend only on the original polynomial count and degree. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance planarCellFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

theorem published_planar_family_uniform_cell_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (S : Set ((ρ ⊕ Fin 2) → ℝ)) (hS : HasPolynomialSignDescription S) :
    ∃ M sOut dOut : ℕ, ∀ p : ρ → ℝ,
      interior (projectionFiber S p) = ∅ →
      (∀ i : Fin 2, BddBelow ((fun x => x i) '' projectionFiber S p)) →
      (∀ i : Fin 2, BddAbove ((fun x => x i) '' projectionFiber S p)) →
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧
        (⋃ j, C j) = projectionFiber S p ∧
        (∀ j, C j = ∅ ∨ (∃ z, C j = {z}) ∨ IsPlanarIntervalGraph (C j)) ∧
        ∀ j, ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card ≤ sOut ∧
          (∀ q ∈ A, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined A (C j) := by
  classical
  have hE := hQE.finite_sign_description _
    (cadUnpackedRelation_definable 2 (hasPolynomialSignDescription_definable hS))
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE 2 univ
    (cadUnpackedRelation 2 S) (hQE.finite_sign_description _ definable_univ) hE
  have hfmt := fun j : d.slicedLeaf => hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (d.slicedFiberCell_definable j))
  choose sp dp hf using hfmt
  let e := Fintype.equivFin d.slicedLeaf
  refine ⟨Fintype.card d.slicedLeaf, Finset.univ.sup sp, Finset.univ.sup dp, ?_⟩
  intro p hthin hlo hhi
  let C : Fin (Fintype.card d.slicedLeaf) → Set (Fin 2 → ℝ) :=
    fun j => projectionFiber (d.slicedFiberCell (e.symm j)) p
  have hsub (j : Fin (Fintype.card d.slicedLeaf)) : C j ⊆ projectionFiber S p := by
    simpa only [cadPackedRelation_unpacked] using d.slicedFiberCell_subset (e.symm j) p
  refine ⟨_, C, le_rfl, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · exact iUnion_subset hsub
    · intro x hx
      have hx' : x ∈ projectionFiber (cadPackedRelation 2 (cadUnpackedRelation 2 S)) p := by
        simpa only [cadPackedRelation_unpacked] using hx
      obtain ⟨j,hj⟩ := d.slicedFiberCell_cover (mem_univ p) hx'
      exact mem_iUnion.mpr ⟨e j, by simpa only [C, e.symm_apply_apply] using hj⟩
  · intro j
    apply d.bounded_thin_planar_slicedFiberCell_cases (e.symm j) p
    · apply Subset.antisymm _ (empty_subset _)
      rw [← hthin]
      exact interior_mono (hsub j)
    · exact fun i => (hlo i).mono (image_mono (hsub j))
    · exact fun i => (hhi i).mono (image_mono (hsub j))
  · intro j
    obtain ⟨A, hc, hd, hA⟩ := hf (e.symm j) p
    exact ⟨A, hc.trans (Finset.le_sup (f := sp) (Finset.mem_univ _)),
      fun q hq => (hd q hq).trans (Finset.le_sup (f := dp) (Finset.mem_univ _)), hA⟩

theorem published_bounded_tuple_planar_cell_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (s D : ℕ) :
    ∃ M sOut dOut : ℕ, ∀ p : Fin s → MvPolynomial (Fin 2) ℝ,
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S → interior S = ∅ →
      (∀ i : Fin 2, BddBelow ((fun x => x i) '' S)) →
      (∀ i : Fin 2, BddAbove ((fun x => x i) '' S)) →
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧ (⋃ j, C j) = S ∧
        (∀ j, C j = ∅ ∨ (∃ z, C j = {z}) ∨ IsPlanarIntervalGraph (C j)) ∧
        ∀ j, ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card ≤ sOut ∧
          (∀ q ∈ A, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined A (C j) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_planar_family_uniform_cell_cover hCAD hQE
      (universalPolynomialBooleanSet (Fin 2) s D b)
      (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D b)
  choose M sp dp hcover using h
  refine ⟨Finset.univ.sup M, Finset.univ.sup sp, Finset.univ.sup dp, ?_⟩
  intro p hp S hS hthin hlo hhi
  obtain ⟨b, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  have he : S = projectionFiber (universalPolynomialBooleanSet (Fin 2) s D b)
      (polynomialFamilyCoefficients D p) := hEq
  rw [he] at hthin hlo hhi ⊢
  obtain ⟨n,C,hn,hunion,hcases,hfmt⟩ := hcover b (polynomialFamilyCoefficients D p) hthin hlo hhi
  refine ⟨n,C,hn.trans (Finset.le_sup (f := M) (Finset.mem_univ b)),hunion,hcases,?_⟩
  intro j
  obtain ⟨A,hc,hd,hA⟩ := hfmt j
  exact ⟨A,hc.trans (Finset.le_sup (f := sp) (Finset.mem_univ b)),
    fun q hq => (hd q hq).trans (Finset.le_sup (f := dp) (Finset.mem_univ b)),hA⟩

/-- Count and piece-image format depend only on the original at-most format.
Zero atoms, degree zero, empty sets and isolated points remain permitted. -/
theorem published_bounded_sign_format_planar_cell_cover
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (s D : ℕ) :
    ∃ M sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      interior S = ∅ → (∀ i : Fin 2, BddBelow ((fun x => x i) '' S)) →
      (∀ i : Fin 2, BddAbove ((fun x => x i) '' S)) →
      ∃ (n : ℕ) (C : Fin n → Set (Fin 2 → ℝ)), n ≤ M ∧ (⋃ j, C j) = S ∧
        (∀ j, C j = ∅ ∨ (∃ z, C j = {z}) ∨ IsPlanarIntervalGraph (C j)) ∧
        ∀ j, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
          (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (C j) := by
  obtain ⟨M,sp,dp,h⟩ := published_bounded_tuple_planar_cell_cover hCAD hQE s D
  refine ⟨M,sp,dp,?_⟩
  intro A S hc hd hS hthin hlo hhi
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp hthin hlo hhi

end PaperI
