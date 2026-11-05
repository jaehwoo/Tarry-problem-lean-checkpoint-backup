import PaperILean.OriginalGaussConditionedBody
import PaperILean.OriginalGaussBodyNeighborhood

/-! I1297-I1305 on the actual path derivative and retained cell section.
The branch is the one already identified with that section, including at
boundary cells. All bounds are at the given point, not on a uniform radius. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

theorem originalAffineHomogeneousVelocity_entry_bound
    (v : Fin 6 → ℝ) (i j : Fin 4) :
    |originalAffineHomogeneousVelocity v i j| ≤ ‖v‖ := by
  have h : ∀ l : Fin 6, |v l| ≤ ‖v‖ := fun l => norm_le_pi_norm v l
  fin_cases i <;> fin_cases j <;> simp [originalAffineHomogeneousVelocity,h,norm_nonneg]

theorem originalGauss_graph_jets_matrix_body_bound
    (c Y : (Fin 2 → ℝ) → ℝ) (q : ℝ → Fin 2 → ℝ) (t : ℝ) (u : Fin 2 → ℝ)
    (hq : HasDerivAt q u t)
    (hc : ContDiffAt ℝ 3 c ![Y (q t),q t 1]) (hY : DifferentiableAt ℝ Y (q t))
    (hr : originalGaussR c ![Y (q t),q t 1] ≠ 0)
    (hright : ∀ᶠ a in 𝓝 (q t), originalGaussCy c ![Y a,a 1]=a 0)
    (M : ℝ) (hM : 1 ≤ M)
    (h2 : ‖fderiv ℝ (fderiv ℝ c) ![Y (q t),q t 1]‖ ≤ M^6)
    (h3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) ![Y (q t),q t 1]‖ ≤ 4*M^10)
    (hi : |(originalGaussR c ![Y (q t),q t 1])⁻¹| ≤ M) :
    ∃ B : Matrix (Fin 4) (Fin 4) ℝ,
      HasDerivAt (fun s => originalAffineHomogeneousMatrix (originalGaussFrameField c Y (q s))) B t ∧
      ∀ i j : Fin 4,
        |((originalAffineHomogeneousMatrix (originalGaussFrameField c Y (q t)))⁻¹*B) i j| ≤
          384*M^33*‖u‖ := by
  obtain ⟨B,hB,he⟩ := originalAffineHomogeneousMatrix_body_derivative
    (fun s => originalGaussFrameField c Y (q s)) _ t
    (originalGaussFrameField_hasDerivAt c Y q t u hq hc hY hr)
  refine ⟨B,hB,?_⟩
  intro i j
  rw [he]
  exact (originalAffineHomogeneousVelocity_entry_bound _ i j).trans
    ((originalGauss_graph_jets_body_bounds c Y (q t) hc hY hr hright M hM h2 h3 hi).2.2.2.2 u)

theorem originalGaussCellSection_coefficient_body_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      C*coefficientEuclideanNorm F ≤ M → ∀ m : ℕ, 2 ≤ m → m ≤ k/2 →
      ∀ {Q : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k (m-1))}
        (A : PlanarGraphRefinement Q) (i : Fin A.refined.count)
        (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ), ContinuousAt c ![y,z] →
      originalNormalLift c ![y,z] ∈ X →
      (∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F (m-1) (originalNormalLift c v)=0) →
      originalNormalPhase F m (originalNormalLift c ![y,z]) ≠ 0 →
      |(originalNormalPhase F m (originalNormalLift c ![y,z]))⁻¹| ≤ M →
      originalGaussR c ![y,z] ≠ 0 → |(originalGaussR c ![y,z])⁻¹| ≤ M →
      (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ)∈projectionFiber (A.refined.domain i) F →
      originalGaussCellSection A F i ![originalGaussCy c ![y,z],z]=![c ![y,z],y] →
      ∃ Y : (Fin 2 → ℝ) → ℝ,
        Y ![originalGaussCy c ![y,z],z]=y ∧
        ContDiffAt ℝ 1 Y ![originalGaussCy c ![y,z],z] ∧
        (∀ᶠ a in 𝓝 (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ), originalGaussCy c ![Y a,a 1]=a 0) ∧
        (∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), Y ![originalGaussCy c v,v 1]=v 0) ∧
        originalGaussCellSection A F i =ᶠ[𝓝[projectionFiber (A.refined.domain i) F] ![originalGaussCy c ![y,z],z]]
          (fun a => (![c ![Y a,a 1],Y a] : Fin 2 → ℝ)) ∧
        (∀ᶠ a in 𝓝 (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ), originalGaussBodyAt c Y a) ∧
        ∀ u : Fin 2 → ℝ,
          ‖originalAffineBodyCoordinates (originalGaussFrameField c Y ![originalGaussCy c ![y,z],z])
            (originalGaussFrameVelocity c Y ![originalGaussCy c ![y,z],z] u)‖ ≤ 384*M^33*‖u‖ := by
  obtain ⟨C,hC,hb⟩ := originalGauss_manuscript_coefficient_body_bounds k X hX
  refine ⟨C,hC,?_⟩
  intro M hM F hF m hm hmk Q A i c y z hc hx hroot hk hki hr hri ha hv
  have he : m-1+1=m := by omega
  have hk' : originalNormalPhase F (m-1+1) (originalNormalLift c ![y,z]) ≠ 0 := by simpa only [he] using hk
  have hcs := originalNormalPhase_same_graph_smooth F (m-1) c ![y,z] hc hroot hk'
  have hc2 : ContDiffAt ℝ 2 c ![y,z] := hcs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨Y,hvY,hY,hR,hL,hagree,hbody⟩ := originalGaussCellSection_body A F i c y z hc2 hroot hk' hr ha hv
  refine ⟨Y,hvY,hY,hR,hL,hagree,hbody,?_⟩
  have hbase : (![Y ![originalGaussCy c ![y,z],z],(![originalGaussCy c ![y,z],z] : Fin 2 → ℝ) 1] : Fin 2 → ℝ)=![y,z] := by simp only [hvY,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have hall := hb M hM F hF m hm hmk c Y ![originalGaussCy c ![y,z],z]
    (by simpa only [hbase] using hc) (by simpa only [hbase] using hx)
    (by simpa only [hbase] using hroot) (by simpa only [hbase] using hk)
    (by simpa only [hbase] using hki) (by simpa only [hbase] using hr)
    (by simpa only [hbase] using hri) (hY.differentiableAt (by norm_num)) hR
  exact hall.2.2.2.2

end PaperI
