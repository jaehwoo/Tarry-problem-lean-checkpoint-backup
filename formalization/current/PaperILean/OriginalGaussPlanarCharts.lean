import PaperILean.PlanarGraphRefinement
import PaperILean.OriginalGaussCommonRootCover

/-! I1317/I1323: actual root charts over planar cells, chosen jointly in the
complete coefficient parameter before original labels or anchors. Refinement
restricts the exact old sections. Cut continuation and quantitative bounds on
conditioned neighborhoods remain separate original-route obligations. -/
noncomputable section
namespace PaperI
open Set FirstOrder Filter
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_originalGauss_planar_root_charts
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (cited : PublishedBivariateNonsingularBezout) (k m : ℕ) (hm : 2≤m) (hmk : m≤k/2) :
    ∃ C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1)),
      Nonempty (PlanarGraphRefinement C) := by
  obtain ⟨C⟩ := published_originalGauss_common_root_cover hCAD hQE cited k m hm hmk
  exact ⟨C,published_planar_graph_refinement hCAD hQE C⟩

theorem originalGauss_planar_charts_exact {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (p z : ℝ) (w : Fin 2 → ℝ) :
    w ∈ originalGaussRegularRootSet F n p z ↔
      ∃ i, ![p,z] ∈ projectionFiber (A.refined.domain i) F ∧
        w = A.refined.sectionMap i (Sum.elim F ![p,z]) :=
  originalGauss_common_root_cover_exact A.refined F p z w

theorem originalGauss_planar_charts_retains_graph {k : ℕ} (m : ℕ)
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1))}
    (A : PlanarGraphRefinement C) (hm : 2≤m) (F : CoefficientSpace k)
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F (m-1) ![c v,v 0,v 1]=0)
    (hk : originalNormalPhase F m ![c ![y,z],y,z]≠0)
    (hr : fderiv ℝ (fun v => fderiv ℝ c v ![1,0]) ![y,z] ![1,0]≠0) :
    ∃ i, ![fderiv ℝ c ![y,z] ![1,0],z] ∈ projectionFiber (A.refined.domain i) F ∧
      ![c ![y,z],y] = A.refined.sectionMap i (Sum.elim F ![fderiv ℝ c ![y,z] ![1,0],z]) :=
  originalGauss_common_root_cover_retains_graph m A.refined hm F c y z hc hroot hk hr

theorem originalGauss_planar_charts_borel {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (i : Fin A.refined.count) :
    MeasurableSet (A.refined.domain i) ∧
      MeasurableSet (selectedFunctionGraph (A.refined.domain i) (A.refined.sectionMap i)) ∧
      Measurable (fun a : A.refined.domain i => A.refined.sectionMap i a) :=
  ⟨A.refined.domain_measurable i,A.refined.graph_measurable i,A.refined.section_measurable i⟩

/-- Existential count and joint domain/graph format bounds depend only on k,
before every m and every phase coefficient. No quantitative radius follows. -/
theorem published_originalGauss_uniform_planar_charts
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (cited : PublishedBivariateNonsingularBezout) (k : ℕ) :
    ∃ N s d : ℕ, ∀ m : ℕ, 2≤m → m≤k/2 →
      ∃ C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1)),
      ∃ A : PlanarGraphRefinement C, A.refined.count≤N ∧
        (∀ i, ∃ B : Finset (MvPolynomial (OriginalGaussParameters k) ℝ),
          B.card≤s ∧ (∀ q ∈ B, q.totalDegree≤d) ∧ PolynomialSignDetermined B (A.refined.domain i)) ∧
        (∀ i, ∃ B : Finset (MvPolynomial (OriginalGaussParameters k ⊕ Fin 2) ℝ),
          B.card≤s ∧ (∀ q ∈ B, q.totalDegree≤d) ∧
            PolynomialSignDetermined B (selectedFunctionGraph (A.refined.domain i) (A.refined.sectionMap i))) := by
  classical
  let I := {m : Fin (k+1) // 2≤m.val ∧ m.val≤k/2}
  let C := fun i : I => Classical.choice
    (published_originalGauss_common_root_cover hCAD hQE cited k i.val.val i.property.1 i.property.2)
  let A := fun i : I => Classical.choice (published_planar_graph_refinement hCAD hQE (C i))
  choose s₁ d₁ h₁ using fun i : I => (A i).common_domain_format
  choose s₂ d₂ h₂ using fun i : I => (A i).refined.common_graph_format
  refine ⟨Finset.univ.sup (fun i : I => (A i).refined.count),
    max (Finset.univ.sup s₁) (Finset.univ.sup s₂),
    max (Finset.univ.sup d₁) (Finset.univ.sup d₂),?_⟩
  intro m hm hmk
  have hmk' : m≤k := hmk.trans (Nat.div_le_self k 2)
  let i : I := ⟨⟨m,by omega⟩,hm,hmk⟩
  refine ⟨C i,A i,Finset.le_sup (f := fun j : I => (A j).refined.count) (Finset.mem_univ i),?_,?_⟩
  · intro j
    obtain ⟨B,hB,hdeg,hS⟩ := h₁ i j
    exact ⟨B,hB.trans ((Finset.le_sup (f := s₁) (Finset.mem_univ i)).trans (le_max_left _ _)),
      fun q hq => (hdeg q hq).trans ((Finset.le_sup (f := d₁) (Finset.mem_univ i)).trans (le_max_left _ _)),hS⟩
  · intro j
    obtain ⟨B,hB,hdeg,hS⟩ := h₂ i j
    exact ⟨B,hB.trans ((Finset.le_sup (f := s₂) (Finset.mem_univ i)).trans (le_max_right _ _)),
      fun q hq => (hdeg q hq).trans ((Finset.le_sup (f := d₂) (Finset.mem_univ i)).trans (le_max_right _ _)),hS⟩

/-- The same refined catalogue has fixed-F planar-domain formats with bounds
chosen before F. Specialization does not increase polynomial count or degree. -/
theorem published_originalGauss_uniform_planar_fiber_format
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    (cited : PublishedBivariateNonsingularBezout) (k : ℕ) :
    ∃ N s d : ℕ, ∀ m : ℕ, 2≤m → m≤k/2 →
      ∃ C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1)),
      ∃ A : PlanarGraphRefinement C, A.refined.count≤N ∧
        ∀ (F : CoefficientSpace k) i, ∃ B : Finset (MvPolynomial (Fin 2) ℝ),
          B.card≤s ∧ (∀ q ∈ B, q.totalDegree≤d) ∧
            PolynomialSignDetermined B (projectionFiber (A.refined.domain i) F) := by
  obtain ⟨N,s,d,h⟩ := published_originalGauss_uniform_planar_charts hCAD hQE cited k
  refine ⟨N,s,d,?_⟩
  intro m hm hmk
  obtain ⟨C,A,hN,hdom,_⟩ := h m hm hmk
  refine ⟨C,A,hN,?_⟩
  intro F i
  obtain ⟨B,hB,hdeg,hS⟩ := hdom i
  exact projectionFiber_has_bounded_sign_format F B (A.refined.domain i) s d hB hdeg hS

end PaperI
