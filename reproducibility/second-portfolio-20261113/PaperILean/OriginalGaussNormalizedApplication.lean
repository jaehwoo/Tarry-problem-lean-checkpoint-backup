import PaperILean.OriginalGaussShearThird

/-! I1301-I1303 on the same inverse and literal retained planar-cell section.
All neighborhoods below are qualitative, with no uniform admissible radius. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

/-- The original normalized identities as a conclusion, never an assumed contract. -/
def originalGaussNormalizedThirdAt (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) : Prop :=
  originalGaussS (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0 = 0 ∧
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0] =
      -originalGaussUUV (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0/originalGaussR c ![Y a,a 1]^2 ∧
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1] =
      -originalGaussUVV (originalGaussGraphPullback (originalGaussFrameField c Y a) c) 0/originalGaussR c ![Y a,a 1]

theorem originalGaussNormalizedThirdAt_of_inverse
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    originalGaussNormalizedThirdAt c Y a :=
  originalGauss_same_shear_original_frame c Y a hc hY hr hright

theorem originalGauss_same_inverse_normalized_neighborhood
    (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 3 c ![Y a,a 1]) (hY : ContDiffAt ℝ 1 Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    ∀ᶠ b in 𝓝 a, originalGaussNormalizedThirdAt c Y b := by
  have hb := (originalGauss_inverse_base_hasFDerivAt Y a
    (hY.differentiableAt (by norm_num))).continuousAt
  have hR := (originalGauss_R_S_differentiableAt c _ hc).1.continuousAt
  filter_upwards [hb.eventually (hc.eventually (by norm_num)),
    hb.eventually (hR.eventually_ne hr),hY.eventually (by norm_num),
    eventually_eventually_nhds.mpr hright] with b hbc hbr hbY hbRight
  exact originalGaussNormalizedThirdAt_of_inverse c Y b hbc
    (hbY.differentiableAt (by norm_num)) hbr hbRight

theorem originalGauss_normalized_body_differential
    (c Y : (Fin 2 → ℝ) → ℝ) (q : ℝ → Fin 2 → ℝ) (t : ℝ) (u : Fin 2 → ℝ)
    (hq : HasDerivAt q u t)
    (hc : ContDiffAt ℝ 3 c ![Y (q t),q t 1]) (hY : DifferentiableAt ℝ Y (q t))
    (hr : originalGaussR c ![Y (q t),q t 1] ≠ 0)
    (hright : ∀ᶠ a in 𝓝 (q t), originalGaussCy c ![Y a,a 1]=a 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ,
      HasDerivAt (fun s => originalAffineHomogeneousMatrix (originalGaussFrameField c Y (q s))) M t ∧
      (originalAffineHomogeneousMatrix (originalGaussFrameField c Y (q t)))⁻¹ * M =
      originalAffineHomogeneousVelocity
        ![u 0,(originalGaussGraphHessian c ![Y (q t),q t 1]).det / originalGaussR c ![Y (q t),q t 1] * u 1,
          0,
          u 0 * (-originalGaussUUV (originalGaussGraphPullback (originalGaussFrameField c Y (q t)) c) 0 /
            originalGaussR c ![Y (q t),q t 1]^2) +
          u 1 * (-originalGaussUVV (originalGaussGraphPullback (originalGaussFrameField c Y (q t)) c) 0 /
            originalGaussR c ![Y (q t),q t 1]),
          u 0 / originalGaussR c ![Y (q t),q t 1],u 1] := by
  obtain ⟨M,hd,hb⟩ := originalGauss_original_body_differential c Y q t u hq hc hY hr hright
  obtain ⟨_,hp,hz⟩ := originalGauss_same_shear_original_frame c Y (q t) hc hY hr hright
  exact ⟨M,hd,by simpa only [hp,hz] using hb⟩

theorem originalGaussCellSection_normalized_third {k n : ℕ}
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
      (∀ᶠ a in 𝓝 (![originalGaussCy c ![y,z],z] : Fin 2 → ℝ),
        originalGaussBodyAt c Y a ∧ originalGaussNormalizedThirdAt c Y a) := by
  obtain ⟨Y,hv,hY,hR,hL,hagree,hbody⟩ := originalGaussCellSection_body A F i c y z hc hroot hk hr ha hbv
  have hcs := originalNormalPhase_same_graph_smooth F n c ![y,z] hc.continuousAt hroot hk
  have hbase : (![Y ![originalGaussCy c ![y,z],z],z] : Fin 2 → ℝ)=![y,z] := by rw [hv]
  have hc3 : ContDiffAt ℝ 3 c ![Y ![originalGaussCy c ![y,z],z],z] := by
    rw [hbase]
    exact hcs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hr' : originalGaussR c ![Y ![originalGaussCy c ![y,z],z],z] ≠ 0 := by rwa [hbase]
  have hn := originalGauss_same_inverse_normalized_neighborhood c Y _ hc3 hY hr' hR
  exact ⟨Y,hv,hY,hR,hL,hagree,hbody.and hn⟩

end PaperI
