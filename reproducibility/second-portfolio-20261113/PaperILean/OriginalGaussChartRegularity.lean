import PaperILean.OriginalGaussSelectedRegularity
import PaperILean.OriginalGaussPlanarCharts

/-! I1287/I1317/I1319: regularity and local uniqueness of the literal refined
catalogue sections. No chart is replaced, no common Borel choice is altered,
and no uniform cut-continuation radius is inferred from qualitative IFT. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

def originalGaussCellSection {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count)
    (a : Fin 2 → ℝ) : Fin 2 → ℝ := A.refined.sectionMap i (Sum.elim F a)

theorem originalGaussCellSection_mem_regular {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count)
    (a : Fin 2 → ℝ) (ha : a∈projectionFiber (A.refined.domain i) F) :
    originalGaussCellSection A F i a∈originalGaussRegularRootSet F n (a 0) (a 1) := by
  have he : (![a 0,a 1] : Fin 2 → ℝ)=a := by ext j; fin_cases j <;> rfl
  apply (originalGauss_planar_charts_exact A F (a 0) (a 1) _).mpr
  rw [he]
  exact ⟨i,ha,rfl⟩

theorem originalGaussCellSection_contDiffOn {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count) :
    ContDiffOn ℝ ∞ (originalGaussCellSection A F i) (projectionFiber (A.refined.domain i) F) :=
  originalGauss_selected_contDiffOn F n _ _ (A.fiber_section_continuousOn i F)
    (originalGaussCellSection_mem_regular A F i)

theorem originalGaussCellSection_local_extension {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count)
    (a : Fin 2 → ℝ) (ha : a∈projectionFiber (A.refined.domain i) F) :
    ∃ b : (Fin 2 → ℝ) → (Fin 2 → ℝ), ∃ U : Set (Fin 2 → ℝ),
      IsOpen U ∧ a∈U ∧ b a=originalGaussCellSection A F i a ∧ ContDiffOn ℝ 1 b U ∧
      (∀ q∈U, originalGaussParameterEquations F n (q,b q)=0) ∧
      EqOn (originalGaussCellSection A F i) b (U∩projectionFiber (A.refined.domain i) F) ∧
      (∀ᶠ u in 𝓝 (a,originalGaussCellSection A F i a),
        originalGaussParameterEquations F n u=0 → u.2=b u.1) :=
  originalGauss_selected_open_extension F n _ _ a ha (A.fiber_section_continuousOn i F a ha)
    (originalGaussCellSection_mem_regular A F i)

theorem originalGaussCellSection_overlap_unique {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i j : Fin A.refined.count)
    (a : Fin 2 → ℝ) (hi : a∈projectionFiber (A.refined.domain i) F)
    (hj : a∈projectionFiber (A.refined.domain j) F)
    (hij : originalGaussCellSection A F i a=originalGaussCellSection A F j a) :
    originalGaussCellSection A F i =ᶠ[𝓝[projectionFiber (A.refined.domain i) F ∩
      projectionFiber (A.refined.domain j) F] a] originalGaussCellSection A F j :=
  originalGauss_selected_overlap_unique F n _ _ _ _ a hi
    (A.fiber_section_continuousOn i F a hi) (A.fiber_section_continuousOn j F a hj) hij
    (originalGaussCellSection_mem_regular A F i) (originalGaussCellSection_mem_regular A F j)

theorem originalGaussCellSection_coordinates_contDiffOn {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun a => originalGaussCellSection A F i a j)
      (projectionFiber (A.refined.domain i) F) := by
  exact (contDiff_apply ℝ ℝ j).comp_contDiffOn (originalGaussCellSection_contDiffOn A F i)

end PaperI
