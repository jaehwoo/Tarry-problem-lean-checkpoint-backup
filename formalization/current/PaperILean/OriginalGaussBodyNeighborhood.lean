import PaperILean.OriginalGaussBodyApplication

/-! I1297-I1299 on a neighborhood of the same branch identified with a
literal retained cell section. No uniform radius or admissibility is asserted. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

/-- The literal matrix body differential, tested on every differentiable path.
This is a definition of the conclusion, not an assumed input contract. -/
def originalGaussBodyAt (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) : Prop :=
  ∀ (q : ℝ → Fin 2 → ℝ) (t : ℝ) (u : Fin 2 → ℝ), q t=a → HasDerivAt q u t →
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ,
      HasDerivAt (fun s => originalAffineHomogeneousMatrix (originalGaussFrameField c Y (q s))) M t ∧
      (originalAffineHomogeneousMatrix (originalGaussFrameField c Y a))⁻¹ * M =
      originalAffineHomogeneousVelocity
        ![u 0,(originalGaussGraphHessian c ![Y a,a 1]).det / originalGaussR c ![Y a,a 1] * u 1,
          0,
          u 0 * fderiv ℝ (fun b => originalGaussShear c ![Y b,b 1]) a ![1,0] +
            u 1 * fderiv ℝ (fun b => originalGaussShear c ![Y b,b 1]) a ![0,1],
          u 0 / originalGaussR c ![Y a,a 1],u 1]

theorem originalGaussBodyAt_of_inverse
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    originalGaussBodyAt c Y a := by
  intro q t u ha hq
  subst a
  exact originalGauss_original_body_differential c Y q t u hq hc hY hr hright

theorem originalGauss_same_inverse_body_neighborhood
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : ContDiffAt ℝ 1 Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    ∀ᶠ b in 𝓝 a, originalGaussBodyAt c Y b := by
  have hb := (originalGauss_inverse_base_hasFDerivAt Y a
    (hY.differentiableAt (by norm_num))).continuousAt
  have hP : ContDiffAt ℝ 2 (originalGaussCy c) ![Y a,a 1] :=
    (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hR : ContinuousAt (originalGaussR c) ![Y a,a 1] :=
    ((hP.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).continuousAt
  filter_upwards [hb.eventually (hc.eventually (by norm_num)),
    hb.eventually (hR.eventually_ne hr),hY.eventually (by norm_num),
    eventually_eventually_nhds.mpr hright] with b hbc hbr hbY hbRight
  exact originalGaussBodyAt_of_inverse c Y b hbc (hbY.differentiableAt (by norm_num)) hbr hbRight

theorem originalGaussCellSection_body {k n : ℕ}
    {C : CylindricalFiniteGraphCover 2 univ (originalGaussJointRegularRelation k n)}
    (A : PlanarGraphRefinement C) (F : CoefficientSpace k) (i : Fin A.refined.count)
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F n ![c v,v 0,v 1]=0)
    (hk : originalNormalPhase F (n+1) ![c ![y,z],y,z] ≠ 0)
    (hr : originalGaussR c ![y,z] ≠ 0)
    (ha : (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ)∈projectionFiber (A.refined.domain i) F)
    (hbv : originalGaussCellSection A F i ![originalGaussCy c ![y,z],z]=![c ![y,z],y]) :
    ∃ Y : (Fin 2 → ℝ) → ℝ,
      Y ![originalGaussCy c ![y,z],z]=y ∧
      ContDiffAt ℝ 1 Y ![originalGaussCy c ![y,z],z] ∧
      (∀ᶠ q in 𝓝 (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ), originalGaussCy c ![Y q,q 1]=q 0) ∧
      (∀ᶠ v in 𝓝 (![y,z] : Fin 2 → ℝ), Y ![originalGaussCy c v,v 1]=v 0) ∧
      originalGaussCellSection A F i =ᶠ[𝓝[projectionFiber (A.refined.domain i) F] ![originalGaussCy c ![y,z],z]]
        (fun q => (![c ![Y q,q 1],Y q] : Fin 2 → ℝ)) ∧
      (∀ᶠ a in 𝓝 (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ), originalGaussBodyAt c Y a) := by
  have hcs := originalNormalPhase_same_graph_smooth F n c ![y,z] hc.continuousAt hroot hk
  obtain ⟨Y,hv,hY,hR,hL,hp,hz,hagree⟩ := originalGaussCellSection_same_inverse A F i c y z hc hroot hr ha hbv
  change Y ![originalGaussCy c ![y,z],z]=y at hv
  refine ⟨Y,hv,hY,hR,hL,hagree,?_⟩
  have hbase : (![Y ![originalGaussCy c ![y,z],z],z] : Fin 2 → ℝ)=![y,z] := by rw [hv]
  apply originalGauss_same_inverse_body_neighborhood c Y _ _ hY _ hR
  · change ContDiffAt ℝ 3 c ![Y ![originalGaussCy c ![y,z],z],z]
    rw [hbase]
    exact hcs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · change originalGaussR c ![Y ![originalGaussCy c ![y,z],z],z] ≠ 0
    rwa [hbase]

end PaperI
