import PaperILean.FrameFirstVariationSmoothness
import PaperILean.GlobalHorizontalFrame

/-! I292-294: differentiate actual criticality along an actual minimizing
frame path. The fixed test is the current symmetric generator S. Exact
recentring identifies the frame contribution with the actual chart Hessian.
The local theorem requires only derivatives at the point and nearby minima;
the final existence theorem applies it to the checked smooth full-interval lift. -/
noncomputable section
open Set Filter
open scoped BigOperators Matrix Matrix.L2OpNorm Topology ContDiff
namespace PaperI

theorem differentiated_criticality_of_horizontal_minima {k : ℕ}
    (F : CoefficientSpace k) (lam : ℝ) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (hpos : 0 < (B t).det)
    (h : PhysicalSpace) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c (B t *ᵥ h) t) (hB : HasDerivAt B (B t * S.val) t)
    (hmin : ∀ᶠ u in 𝓝 t, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val) :
    symmetricFrameEnergyHessian F (c t) lam ⟨B t, hpos⟩ S S =
      -4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F (c t) (B t) h S.val r := by
  let Bt : PositiveFrame := ⟨B t, hpos⟩
  have hd := ((contDiffAt_frameFirstVariation F (c t) lam Bt S.val).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t (hc.prodMk hB)
  have he : (fun u => frameFirstVariation F lam S.val (c u, B u)) =ᶠ[𝓝 t]
      fun _ => (0 : ℝ) := by
    filter_upwards [hmin] with u hu
    exact frameFirstVariation_zero_of_minimum F (c u) lam ⟨B u, hu.1⟩ S.val S.property hu.2
  have hz := hd.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)
  have hsplit : (B t *ᵥ h, B t * S.val) =
      (B t *ᵥ h, 0) + (0, B t * S.val) := by simp
  rw [hsplit, map_add, fderiv_frameFirstVariation_center F (c t) lam Bt h S.val S.property,
    fderiv_frameFirstVariation_frame_diag F (c t) lam Bt S] at hz
  dsimp only [Bt] at hz
  linarith

theorem differentiated_criticality_on_open {k : ℕ}
    (F : CoefficientSpace k) (lam : ℝ) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : Set ℝ} (hs : IsOpen s)
    (hmin : ∀ u ∈ s, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val)
    {t : ℝ} (ht : t ∈ s) (h : PhysicalSpace) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c (B t *ᵥ h) t) (hB : HasDerivAt B (B t * S.val) t) :
    symmetricFrameEnergyHessian F (c t) lam ⟨B t, (hmin t ht).1⟩ S S =
      -4 * ∑ r ∈ Finset.Icc 2 (k - 1), jetCenterFrameMixedTerm F (c t) (B t) h S.val r := by
  apply differentiated_criticality_of_horizontal_minima F lam c B t (hmin t ht).1 h S hc hB
  filter_upwards [hs.mem_nhds ht] with u hu
  exact hmin u hu

theorem hasDerivAt_center_normalized_velocity (c : ℝ → PhysicalSpace)
    {t : ℝ} {v : PhysicalSpace} (hc : HasDerivAt c v t)
    (B : PositiveFrame) : HasDerivAt c (B.val *ᵥ (B.val⁻¹ *ᵥ v)) t := by
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B.val (isUnit_iff_ne_zero.mpr B.property.ne'),
    Matrix.one_mulVec] using hc

theorem differentiated_criticality_normalized_velocity {k : ℕ}
    (F : CoefficientSpace k) (lam : ℝ) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : Set ℝ} (hs : IsOpen s)
    (hmin : ∀ u ∈ s, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val)
    {t : ℝ} (ht : t ∈ s) (v : PhysicalSpace) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c v t) (hB : HasDerivAt B (B t * S.val) t) :
    symmetricFrameEnergyHessian F (c t) lam ⟨B t, (hmin t ht).1⟩ S S =
      -4 * ∑ r ∈ Finset.Icc 2 (k - 1),
        jetCenterFrameMixedTerm F (c t) (B t) ((B t)⁻¹ *ᵥ v) S.val r :=
  differentiated_criticality_on_open F lam c B hs hmin ht ((B t)⁻¹ *ᵥ v) S
    (hasDerivAt_center_normalized_velocity c hc ⟨B t, (hmin t ht).1⟩) hB

theorem exists_horizontal_minimizingFrame_with_criticality {k : ℕ}
    (F : CoefficientSpace k) (c : ℝ → PhysicalSpace) {s : Set ℝ}
    (hs : IsOpen s) (hi : Icc (0 : ℝ) 1 ⊆ s) (hc : ContDiffOn ℝ ∞ c s)
    (lam : ℝ) (hlam : 0 < lam) (B₀ : PositiveFrame)
    (hmin : ∀ D : PositiveFrame, FrameEnergy F (c 0) lam B₀.val ≤
      FrameEnergy F (c 0) lam D.val) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ s ∧
      ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        B 0 = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo a b) ∧
        ∀ t ∈ Ioo a b, ∃ hpos : 0 < (B t).det,
          (∀ D : PositiveFrame, FrameEnergy F (c t) lam (B t) ≤ FrameEnergy F (c t) lam D.val) ∧
          ∃ S : SymmetricMatrix 3, HasDerivAt B (B t * S.val) t ∧
            symmetricFrameEnergyHessian F (c t) lam ⟨B t, hpos⟩ S S =
              -4 * ∑ r ∈ Finset.Icc 2 (k - 1),
                jetCenterFrameMixedTerm F (c t) (B t) ((B t)⁻¹ *ᵥ deriv c t) S.val r := by
  obtain ⟨a, b, ha, hb, hab, B, hB₀, hsm, hB⟩ :=
    exists_horizontal_minimizingFrame_covering_unitInterval F c hs hi hc lam hlam B₀ hmin
  have hm : ∀ u ∈ Ioo a b, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val :=
    fun u hu => ⟨(hB u hu).1, (hB u hu).2.1⟩
  refine ⟨a, b, ha, hb, hab, B, hB₀, hsm, ?_⟩
  intro t ht
  obtain ⟨hp, hmt, S, hS, hd⟩ := hB t ht
  refine ⟨hp, hmt, ⟨S, hS⟩, hd, ?_⟩
  have hct : HasDerivAt c (deriv c t) t :=
    ((hc.differentiableOn (by simp)) t (hab (Ioo_subset_Icc_self ht))).differentiableAt
      (hs.mem_nhds (hab (Ioo_subset_Icc_self ht))) |>.hasDerivAt
  exact differentiated_criticality_normalized_velocity F lam c B isOpen_Ioo hm ht
    (deriv c t) ⟨S, hS⟩ hct hd

end PaperI
