import PaperILean.OriginalNormalGraphSmooth

/-! The original I1297-I1299 body differential, on the same inverse branch.
All six affine coordinates and the genuine homogeneous matrix derivative are
retained. The last theorem applies it to the literal retained cell section. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

def originalGaussGraphHessian (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![originalGaussR c v,originalGaussS c v;
    fderiv ℝ (originalGaussCz c) v ![1,0],originalGaussT c v]

theorem originalGaussGraphHessian_det (c : (Fin 2 → ℝ) → ℝ)
    (v : Fin 2 → ℝ) (hc : ContDiffAt ℝ 2 c v) :
    (originalGaussGraphHessian c v).det =
      originalGaussR c v * originalGaussT c v - originalGaussS c v^2 := by
  simp only [originalGaussGraphHessian,Matrix.det_fin_two_of,
    originalGauss_mixed_partials c v hc]
  ring

def originalGaussFrameField (c Y : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) : Fin 6 → ℝ :=
  originalGaussNormalFrame (a 0) (a 1) (c ![Y a,a 1]) (Y a)
    (originalGaussCz c ![Y a,a 1]) (originalGaussShear c ![Y a,a 1])

def originalGaussFrameVelocity (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![u 0,
    fderiv ℝ (fun q => originalGaussCz c ![Y q,q 1]) a u +
      fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a u * a 0 +
      originalGaussShear c ![Y a,a 1] * u 0,
    fderiv ℝ (fun q => c ![Y q,q 1]) a u,
    fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a u,
    fderiv ℝ Y a u,u 1]

theorem originalGaussFrameField_hasDerivAt
    (c Y : (Fin 2 → ℝ) → ℝ) (q : ℝ → Fin 2 → ℝ) (t : ℝ) (u : Fin 2 → ℝ)
    (hq : HasDerivAt q u t)
    (hc : ContDiffAt ℝ 3 c ![Y (q t),q t 1]) (hY : DifferentiableAt ℝ Y (q t))
    (hr : originalGaussR c ![Y (q t),q t 1] ≠ 0) :
    HasDerivAt (fun s => originalGaussFrameField c Y (q s))
      (originalGaussFrameVelocity c Y (q t) u) t := by
  have hbase := (originalGauss_inverse_base_hasFDerivAt Y (q t) hY).differentiableAt
  have hC : DifferentiableAt ℝ (fun a : Fin 2 → ℝ => c ![Y a,a 1]) (q t) :=
    (hc.differentiableAt (by norm_num)).comp (q t) hbase
  have hQ : DifferentiableAt ℝ (fun a : Fin 2 → ℝ => originalGaussCz c ![Y a,a 1]) (q t) := by
    have hd : DifferentiableAt ℝ (originalGaussCz c) ![Y (q t),q t 1] :=
      ((hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
    exact DifferentiableAt.comp (f := fun a : Fin 2 → ℝ => (![Y a,a 1] : Fin 2 → ℝ)) (q t) hd hbase
  have hD : DifferentiableAt ℝ (fun a : Fin 2 → ℝ => originalGaussShear c ![Y a,a 1]) (q t) :=
    DifferentiableAt.comp (f := fun a : Fin 2 → ℝ => (![Y a,a 1] : Fin 2 → ℝ)) (q t)
      (originalGauss_shear_differentiableAt c _ hc hr) hbase
  have hCv := hC.hasFDerivAt.comp_hasDerivAt t hq
  have hQv := hQ.hasFDerivAt.comp_hasDerivAt t hq
  have hDv := hD.hasFDerivAt.comp_hasDerivAt t hq
  have hYv := hY.hasFDerivAt.comp_hasDerivAt t hq
  have hp := hasDerivAt_pi.mp hq 0
  have hz := hasDerivAt_pi.mp hq 1
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hp
  · simpa only [originalGaussFrameField,originalGaussNormalFrame,originalGaussFrameVelocity,
      Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val_zero,add_assoc] using hQv.add (hDv.mul hp)
  · exact hCv
  · exact hDv
  · exact hYv
  · exact hz

theorem originalGaussFrameField_body_coordinates
    (c Y : (Fin 2 → ℝ) → ℝ) (a u : Fin 2 → ℝ)
    (hc : ContDiffAt ℝ 2 c ![Y a,a 1]) (hY : DifferentiableAt ℝ Y a)
    (hr : originalGaussR c ![Y a,a 1] ≠ 0)
    (hright : ∀ᶠ q in 𝓝 a, originalGaussCy c ![Y q,q 1]=q 0) :
    originalAffineBodyCoordinates (originalGaussFrameField c Y a)
      (originalGaussFrameVelocity c Y a u) =
      ![u 0, (originalGaussGraphHessian c ![Y a,a 1]).det / originalGaussR c ![Y a,a 1] * u 1,
        0,
        u 0 * fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![1,0] +
          u 1 * fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a ![0,1],
        u 0 / originalGaussR c ![Y a,a 1],u 1] := by
  have hy := originalGauss_same_inverse_fderiv c Y a u hc hY hr hright
  have hq := originalGauss_same_q0_fderiv c Y a u hc hY hr hright
  have hg := originalGauss_same_graph_fderiv c Y a u (hc.differentiableAt (by norm_num)) hY hright.self_of_nhds
  have hd := originalGauss_linear_apply_two (fderiv ℝ (fun q => originalGaussShear c ![Y q,q 1]) a) u
  rw [originalGaussGraphHessian_det c _ hc]
  ext i
  fin_cases i <;>
    simp [originalAffineBodyCoordinates,originalGaussFrameField,originalGaussNormalFrame,
      originalGaussFrameVelocity,hq,hg,hy,hd] <;> ring

theorem originalGauss_original_body_differential
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
          u 0 * fderiv ℝ (fun a => originalGaussShear c ![Y a,a 1]) (q t) ![1,0] +
            u 1 * fderiv ℝ (fun a => originalGaussShear c ![Y a,a 1]) (q t) ![0,1],
          u 0 / originalGaussR c ![Y (q t),q t 1],u 1] := by
  obtain ⟨M,hM,hbody⟩ := originalAffineHomogeneousMatrix_body_derivative
    (fun s => originalGaussFrameField c Y (q s)) _ t
    (originalGaussFrameField_hasDerivAt c Y q t u hq hc hY hr)
  refine ⟨M,hM,?_⟩
  have hc2 : ContDiffAt ℝ 2 c ![Y (q t),q t 1] := hc.of_le (by decide)
  rw [originalGaussFrameField_body_coordinates c Y (q t) u hc2 hY hr hright] at hbody
  exact hbody

end PaperI
