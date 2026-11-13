import PaperILean.JointPlanarCellCover

/-! Refine every old chart domain, retaining its literal section function.
The finite family is chosen jointly in all parameters. It is a cover; no
disjointness or continuity between different cells is asserted. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure PlanarGraphRefinement {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) where
  refined : CylindricalFiniteGraphCover n P R
  parent : Fin refined.count → Fin C.count
  domain_subset_parent : ∀ i, refined.domain i ⊆ C.domain (parent i)
  section_eq_parent : ∀ i, refined.sectionMap i = C.sectionMap (parent i)
  retains : ∀ j a, a ∈ C.domain j → ∃ i, parent i = j ∧ a ∈ refined.domain i
  fiber_cell : ∀ i p, projectionFiber (refined.domain i) p = ∅ ∨
    IsPlanarCylindricalCell (projectionFiber (refined.domain i) p)

theorem published_planar_graph_refinement
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    (C : CylindricalFiniteGraphCover n P R) : Nonempty (PlanarGraphRefinement C) := by
  classical
  let D := fun j => Classical.choice (published_joint_planar_cell_cover hCAD hQE
    (C.domain j) (C.domain_sign j))
  let J := (j : Fin C.count) × Fin (D j).count
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin _).symm
  let A : CylindricalFiniteGraphCover n P R :=
    { count := Fintype.card J
      domain := fun i => (D (e i).1).cell (e i).2
      sectionMap := fun i => C.sectionMap (e i).1
      domain_subset := fun i => ((D (e i).1).cell_subset (e i).2).trans (C.domain_subset (e i).1)
      domain_sign := fun i => (D (e i).1).cell_sign (e i).2
      graph_sign := fun i => selectedFunctionGraph_restrict
        ((D (e i).1).cell_subset (e i).2) _ ((D (e i).1).cell_sign (e i).2) (C.graph_sign (e i).1)
      continuousOn := fun i => (C.continuousOn (e i).1).mono ((D (e i).1).cell_subset (e i).2)
      cover := by
        intro a ha x
        rw [C.cover a ha x]
        constructor
        · rintro ⟨j,hj,hx⟩
          obtain ⟨t,ht⟩ := ((D j).cover a).mp hj
          exact ⟨e.symm ⟨j,t⟩,by
            have h := congrArg (fun q : J => (D q.1).cell q.2) (e.apply_symm_apply ⟨j,t⟩)
            exact (Set.ext_iff.mp h a).mpr ht,
            by simpa only [Equiv.apply_symm_apply] using hx⟩
        · rintro ⟨i,hi,hx⟩
          exact ⟨(e i).1,(D (e i).1).cell_subset (e i).2 hi,hx⟩ }
  refine ⟨{ refined := A
            parent := fun i => (e i).1
            domain_subset_parent := fun i => (D (e i).1).cell_subset (e i).2
            section_eq_parent := fun _ => rfl
            fiber_cell := fun i p => (D (e i).1).fiber_cell (e i).2 p
            retains := ?_ }⟩
  intro j a ha
  obtain ⟨t,ht⟩ := ((D j).cover a).mp ha
  exact ⟨e.symm ⟨j,t⟩,by simp only [Equiv.apply_symm_apply],
    by
      have h := congrArg (fun q : J => (D q.1).cell q.2) (e.apply_symm_apply ⟨j,t⟩)
      exact (Set.ext_iff.mp h a).mpr ht⟩

theorem PlanarGraphRefinement.retains_section {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    {C : CylindricalFiniteGraphCover n P R} (A : PlanarGraphRefinement C)
    (j : Fin C.count) {a : (ρ ⊕ Fin 2) → ℝ} (ha : a ∈ C.domain j) :
    ∃ i, a ∈ A.refined.domain i ∧ A.parent i = j ∧
      A.refined.sectionMap i a = C.sectionMap j a := by
  obtain ⟨i,hi,hmem⟩ := A.retains j a ha
  exact ⟨i,hmem,hi,by rw [A.section_eq_parent i,hi]⟩

theorem PlanarGraphRefinement.domain_union {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    {C : CylindricalFiniteGraphCover n P R} (A : PlanarGraphRefinement C)
    (j : Fin C.count) :
    (⋃ i : {i : Fin A.refined.count // A.parent i = j}, A.refined.domain i.val) = C.domain j := by
  ext a
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    have h := A.domain_subset_parent i.val hi
    rwa [i.property] at h
  · intro ha
    obtain ⟨i,hi,hmem⟩ := A.retains j a ha
    exact ⟨⟨i,hi⟩,hmem⟩

theorem PlanarGraphRefinement.common_domain_format {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    {C : CylindricalFiniteGraphCover n P R} (A : PlanarGraphRefinement C) :
    ∃ s d : ℕ, ∀ i, ∃ B : Finset (MvPolynomial (ρ ⊕ Fin 2) ℝ),
      B.card ≤ s ∧ (∀ q ∈ B, q.totalDegree ≤ d) ∧
      PolynomialSignDetermined B (A.refined.domain i) :=
  finite_sign_descriptions_common_format _ A.refined.domain_sign

theorem PlanarGraphRefinement.fiber_section_continuousOn {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    {C : CylindricalFiniteGraphCover n P R} (A : PlanarGraphRefinement C)
    (i : Fin A.refined.count) (p : ρ → ℝ) :
    ContinuousOn (fun x : Fin 2 → ℝ => A.refined.sectionMap i (Sum.elim p x))
      (projectionFiber (A.refined.domain i) p) := by
  have h : Continuous (fun x : Fin 2 → ℝ => Sum.elim p x) := by
    apply continuous_pi
    intro j
    cases j with
    | inl a => exact continuous_const
    | inr a => exact continuous_apply a
  exact (A.refined.continuousOn i).comp h.continuousOn (fun _ hx => hx)

theorem PlanarGraphRefinement.common_fiber_domain_format {ρ : Type} {n : ℕ}
    {P : Set ((ρ ⊕ Fin 2) → ℝ)} {R : Set (((ρ ⊕ Fin 2) ⊕ Fin n) → ℝ)}
    {C : CylindricalFiniteGraphCover n P R} (A : PlanarGraphRefinement C) :
    ∃ s d : ℕ, ∀ i p, ∃ B : Finset (MvPolynomial (Fin 2) ℝ),
      B.card ≤ s ∧ (∀ q ∈ B, q.totalDegree ≤ d) ∧
      PolynomialSignDetermined B (projectionFiber (A.refined.domain i) p) := by
  classical
  have h := fun i => hasPolynomialSignDescription_uniform_fiber_sign_format (A.refined.domain_sign i)
  choose s d hfmt using h
  refine ⟨Finset.univ.sup s,Finset.univ.sup d,?_⟩
  intro i p
  obtain ⟨B,hB,hdeg,hS⟩ := hfmt i p
  exact ⟨B,hB.trans (Finset.le_sup (f := s) (Finset.mem_univ i)),
    fun q hq => (hdeg q hq).trans (Finset.le_sup (f := d) (Finset.mem_univ i)),hS⟩

end PaperI
