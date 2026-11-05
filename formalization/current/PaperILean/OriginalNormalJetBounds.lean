import PaperILean.OriginalNormalThirdRecursion

/-! I1305: uniform numerical consequences of the original implicit recursion.
M is fixed before the phase, graph and base point. Phase derivative bounds and
normal inverse conditioning are explicit; graph derivative bounds are proved. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem originalNormal_norm_normal (a : ℝ) : ‖(![a,0,0] : Fin 3 → ℝ)‖=|a| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg a)).mpr
    intro i; fin_cases i <;> simp [Real.norm_eq_abs]
  · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a,0,0] : Fin 3 → ℝ) 0

theorem originalNormal_norm_tangent (u : Fin 2 → ℝ) :
    ‖(![0,u 0,u 1] : Fin 3 → ℝ)‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro i; fin_cases i
  · simp
  · exact norm_le_pi_norm u 0
  · exact norm_le_pi_norm u 1

theorem originalNormal_abs_of_root_equation (x k b : ℝ) (hk : k ≠ 0)
    (he : x*k+b=0) : |x| = |k⁻¹| * |b| := by
  have hx : x = -b*k⁻¹ := by field_simp [hk]; nlinarith
  rw [hx,abs_mul,abs_neg]; ring

theorem originalNormalLiftLinear_norm_le
    (c : (Fin 2 → ℝ) → ℝ) (v u : Fin 2 → ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hc : ‖fderiv ℝ c v‖ ≤ L) :
    ‖originalNormalLiftLinear c v u‖ ≤ L*‖u‖ := by
  rw [originalNormalLiftLinear_apply]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg u))).mpr
  intro i; fin_cases i
  · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg u))
  · exact (norm_le_pi_norm u 0).trans (by nlinarith [norm_nonneg u])
  · exact (norm_le_pi_norm u 1).trans (by nlinarith [norm_nonneg u])

theorem originalNormalLiftSecond_norm_le
    (c : (Fin 2 → ℝ) → ℝ) (v u w : Fin 2 → ℝ) (H : ℝ)
    (hc : ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ H) :
    ‖originalNormalLiftSecond c v u w‖ ≤ H*‖w‖*‖u‖ := by
  rw [originalNormalLiftSecond,originalNormal_norm_normal,← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm₂ _ _ _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (norm_nonneg w)) (norm_nonneg u))

theorem originalNormal_first_norm_bound
    (M : ℝ) (hM : 1 ≤ M)
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hG : DifferentiableAt ℝ G (originalNormalLift c v)) (hc : DifferentiableAt ℝ c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0)
    (hk : fderiv ℝ G (originalNormalLift c v) ![1,0,0] ≠ 0)
    (hki : |(fderiv ℝ G (originalNormalLift c v) ![1,0,0])⁻¹| ≤ M)
    (hG1 : ‖fderiv ℝ G (originalNormalLift c v)‖ ≤ M) :
    ‖fderiv ℝ c v‖ ≤ M^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg M)
  intro u
  rw [Real.norm_eq_abs,originalNormal_abs_of_root_equation _ _ _ hk
    (originalNormal_root_first_equation G c v u hG hc hroot)]
  calc
    _ ≤ M * |fderiv ℝ G (originalNormalLift c v) ![0,u 0,u 1]| :=
      mul_le_mul_of_nonneg_right hki (abs_nonneg _)
    _ ≤ M * (M*‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hG1 (originalNormal_norm_tangent u) (norm_nonneg _) (by linarith))
    _ = _ := by ring

theorem originalNormal_second_norm_bound
    (M : ℝ) (hM : 1 ≤ M)
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 2 G (originalNormalLift c v)) (hc : ContDiffAt ℝ 2 c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0)
    (hk : fderiv ℝ G (originalNormalLift c v) ![1,0,0] ≠ 0)
    (hki : |(fderiv ℝ G (originalNormalLift c v) ![1,0,0])⁻¹| ≤ M)
    (hG2 : ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ ≤ M)
    (hc1 : ‖fderiv ℝ c v‖ ≤ M^2) :
    ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6 := by
  have hM0 : 0 ≤ M := by linarith
  have hM2 : 1 ≤ M^2 := one_le_pow₀ hM
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hM0 _)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (pow_nonneg hM0 _) (norm_nonneg w))
  intro u
  have he := originalNormal_root_second_identity G c v u w hG hc hroot
  rw [add_comm] at he
  rw [Real.norm_eq_abs,originalNormal_abs_of_root_equation _ _ _ hk he]
  calc
    _ ≤ M * |fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
      (originalNormalLiftLinear c v w) (originalNormalLiftLinear c v u)| :=
      mul_le_mul_of_nonneg_right hki (abs_nonneg _)
    _ ≤ M * (M*(M^2*‖w‖)*(M^2*‖u‖)) := by
      apply mul_le_mul_of_nonneg_left _ hM0
      rw [← Real.norm_eq_abs]
      apply (ContinuousLinearMap.le_opNorm₂ _ _ _).trans
      exact mul_le_mul (mul_le_mul hG2 (originalNormalLiftLinear_norm_le c v w _ hM2 hc1)
        (norm_nonneg _) hM0) (originalNormalLiftLinear_norm_le c v u _ hM2 hc1)
        (norm_nonneg _) (mul_nonneg hM0 (mul_nonneg (sq_nonneg M) (norm_nonneg w)))
    _ = _ := by ring

theorem originalNormal_trilinear_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (z w u : E) :
    ‖L z w u‖ ≤ ‖L‖*‖z‖*‖w‖*‖u‖ := by
  exact (ContinuousLinearMap.le_opNorm₂ (L z) w u).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (L.le_opNorm z) (norm_nonneg w)) (norm_nonneg u))

theorem originalNormal_third_norm_bound
    (M : ℝ) (hM : 1 ≤ M)
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 3 G (originalNormalLift c v)) (hc : ContDiffAt ℝ 3 c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0)
    (hk : fderiv ℝ G (originalNormalLift c v) ![1,0,0] ≠ 0)
    (hki : |(fderiv ℝ G (originalNormalLift c v) ![1,0,0])⁻¹| ≤ M)
    (hG2 : ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ ≤ M)
    (hG3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (originalNormalLift c v)‖ ≤ M)
    (hc1 : ‖fderiv ℝ c v‖ ≤ M^2) (hc2 : ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ 4*M^10 := by
  have hM0 : 0 ≤ M := by linarith
  have hM2 : 1 ≤ M^2 := one_le_pow₀ hM
  have hL := originalNormalLiftLinear_norm_le c v
  have hH := originalNormalLiftSecond_norm_le c v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  let A := fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (originalNormalLift c v)
    (originalNormalLiftLinear c v z) (originalNormalLiftLinear c v w) (originalNormalLiftLinear c v u)
  let B := fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
    (originalNormalLiftSecond c v w z) (originalNormalLiftLinear c v u)
  let C := fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
    (originalNormalLiftLinear c v w) (originalNormalLiftSecond c v u z)
  let D := fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)
    (originalNormalLiftLinear c v z) (originalNormalLiftSecond c v u w)
  have hA : |A| ≤ M^7*‖z‖*‖w‖*‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (originalNormalLift c v)‖ *
          ‖originalNormalLiftLinear c v z‖*‖originalNormalLiftLinear c v w‖*‖originalNormalLiftLinear c v u‖ :=
        originalNormal_trilinear_norm _ _ _ _
      _ ≤ M*(M^2*‖z‖)*(M^2*‖w‖)*(M^2*‖u‖) := by
        gcongr
        · exact hL z _ hM2 hc1
        · exact hL w _ hM2 hc1
        · exact hL u _ hM2 hc1
      _ = _ := by ring
  have hB : |B| ≤ M^9*‖z‖*‖w‖*‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ *
          ‖originalNormalLiftSecond c v w z‖*‖originalNormalLiftLinear c v u‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M*(M^6*‖z‖*‖w‖)*(M^2*‖u‖) := by
        gcongr
        · exact hH w z _ hc2
        · exact hL u _ hM2 hc1
      _ = _ := by ring
  have hC : |C| ≤ M^9*‖z‖*‖w‖*‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ *
          ‖originalNormalLiftLinear c v w‖*‖originalNormalLiftSecond c v u z‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M*(M^2*‖w‖)*(M^6*‖z‖*‖u‖) := by
        gcongr
        · exact hL w _ hM2 hc1
        · exact hH u z _ hc2
      _ = _ := by ring
  have hD : |D| ≤ M^9*‖z‖*‖w‖*‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ *
          ‖originalNormalLiftLinear c v z‖*‖originalNormalLiftSecond c v u w‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M*(M^2*‖z‖)*(M^6*‖w‖*‖u‖) := by
        gcongr
        · exact hL z _ hM2 hc1
        · exact hH u w _ hc2
      _ = _ := by ring
  have he := originalNormal_root_third_identity G c v u w z hG hc hroot
  change A+B+C+D+_ = 0 at he
  have he' : fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v z w u *
      fderiv ℝ G (originalNormalLift c v) ![1,0,0] + (A+B+C+D)=0 := by linarith
  rw [Real.norm_eq_abs,originalNormal_abs_of_root_equation _ _ _ hk he']
  calc
    _ ≤ M*|A+B+C+D| := mul_le_mul_of_nonneg_right hki (abs_nonneg _)
    _ ≤ M*(|A|+|B|+|C|+|D|) := by
      apply mul_le_mul_of_nonneg_left _ hM0
      exact (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)
    _ ≤ M*(M^7*‖z‖*‖w‖*‖u‖+M^9*‖z‖*‖w‖*‖u‖+
        M^9*‖z‖*‖w‖*‖u‖+M^9*‖z‖*‖w‖*‖u‖) := by gcongr
    _ = (M^8+3*M^10)*‖z‖*‖w‖*‖u‖ := by ring
    _ ≤ (4*M^10)*‖z‖*‖w‖*‖u‖ := by
      gcongr
      have hp : M^8 ≤ M^10 := pow_le_pow_right₀ hM (by omega)
      linarith

theorem originalNormal_jet_norm_bounds
    (M : ℝ) (hM : 1 ≤ M)
    (G : (Fin 3 → ℝ) → ℝ) (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ)
    (hG : ContDiffAt ℝ 3 G (originalNormalLift c v)) (hc : ContDiffAt ℝ 3 c v)
    (hroot : ∀ᶠ t in 𝓝 v, G (originalNormalLift c t)=0)
    (hk : fderiv ℝ G (originalNormalLift c v) ![1,0,0] ≠ 0)
    (hki : |(fderiv ℝ G (originalNormalLift c v) ![1,0,0])⁻¹| ≤ M)
    (hG1 : ‖fderiv ℝ G (originalNormalLift c v)‖ ≤ M)
    (hG2 : ‖fderiv ℝ (fderiv ℝ G) (originalNormalLift c v)‖ ≤ M)
    (hG3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (originalNormalLift c v)‖ ≤ M) :
    ‖fderiv ℝ c v‖ ≤ M^2 ∧ ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6 ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ 4*M^10 := by
  have h1 := originalNormal_first_norm_bound M hM G c v (hG.differentiableAt (by norm_num))
    (hc.differentiableAt (by norm_num)) hroot hk hki hG1
  have h2 := originalNormal_second_norm_bound M hM G c v (hG.of_le (by decide))
    (hc.of_le (by decide)) hroot hk hki hG2 h1
  exact ⟨h1,h2,originalNormal_third_norm_bound M hM G c v hG hc hroot hk hki hG2 hG3 h1 h2⟩

end PaperI
