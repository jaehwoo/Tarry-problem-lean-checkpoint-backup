import PaperILean.MovingFrameCriticality
import PaperILean.ComparisonDifferentialBound

/-! I296: discharge the previously explicit differentiated-criticality premise
for actual horizontal minimizing paths. Uniform K is chosen before R,F and all
paths, times and generators; the tensor norm and regularization are unchanged.
This does not prove I298's quantitative bootstrap or ellipsoid comparison. -/
noncomputable section
open Set Filter
open scoped BigOperators Matrix Matrix.L2OpNorm Topology ContDiff
namespace PaperI

theorem horizontal_generator_bound_along_minima {k : ℕ}
    (F : CoefficientSpace k) (lam : ℝ) (hlam : 0 < lam) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : Set ℝ} (hs : IsOpen s)
    (hmin : ∀ u ∈ s, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val)
    {t : ℝ} (ht : t ∈ s) (h : PhysicalSpace) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c (B t *ᵥ h) t) (hB : HasDerivAt B (B t * S.val) t)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F (c t) (B t) r ≤ M) :
    matrixFullHSNorm S.val ≤ (4 * ((k : ℝ) + 1) * M) / Real.sqrt lam * physicalEuclideanNorm h :=
  horizontal_generator_bound_of_criticality F (c t) lam hlam ⟨B t, (hmin t ht).1⟩ h S M hM0 hM
    (differentiated_criticality_on_open F lam c B hs hmin ht h S hc hB)

theorem source_horizontal_generator_bound_along_minima (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : ℝ → PhysicalSpace,
      ∀ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ, ∀ s : Set ℝ, IsOpen s →
      (∀ u ∈ s, 0 < (B u).det ∧ ∀ D : PositiveFrame,
        FrameEnergy F (c u) (sourceRegularization CX C0 R) (B u) ≤
          FrameEnergy F (c u) (sourceRegularization CX C0 R) D.val) →
      ∀ t ∈ s, c t ∈ X → ∀ h : PhysicalSpace, ∀ S : SymmetricMatrix 3,
      HasDerivAt c (B t *ᵥ h) t → HasDerivAt B (B t * S.val) t →
      matrixFullHSNorm S.val ≤ K / Real.sqrt (sourceRegularization CX C0 R) * physicalEuclideanNorm h := by
  obtain ⟨K, hK, hw⟩ := source_horizontal_generator_bound_of_criticality k X hX CX C0 hCX hC0
  refine ⟨K, hK, ?_⟩
  intro R hR F hF c B s hs hm t ht hct h S hc hB
  exact hw R hR F hF (c t) hct ⟨B t, (hm t ht).1⟩ (hm t ht).2 h S
    (differentiated_criticality_on_open F _ c B hs hm ht h S hc hB)

theorem exists_source_horizontal_minimizingFrame_with_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) (CX C0 : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 2 ≤ R → ∀ F : CoefficientSpace k,
      coefficientEuclideanNorm F ≤ 2 * R → ∀ c : ℝ → PhysicalSpace,
      ∀ s : Set ℝ, IsOpen s → Icc (0 : ℝ) 1 ⊆ s → ContDiffOn ℝ ∞ c s →
      ∀ B₀ : PositiveFrame,
      (∀ D : PositiveFrame, FrameEnergy F (c 0) (sourceRegularization CX C0 R) B₀.val ≤
        FrameEnergy F (c 0) (sourceRegularization CX C0 R) D.val) →
      ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ s ∧
        ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
          B 0 = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo a b) ∧
          ∀ t ∈ Ioo a b, 0 < (B t).det ∧
            (∀ D : PositiveFrame, FrameEnergy F (c t) (sourceRegularization CX C0 R) (B t) ≤
              FrameEnergy F (c t) (sourceRegularization CX C0 R) D.val) ∧
            ∃ S : SymmetricMatrix 3, HasDerivAt B (B t * S.val) t ∧
              (c t ∈ X → matrixFullHSNorm S.val ≤ K / Real.sqrt (sourceRegularization CX C0 R) *
                physicalEuclideanNorm ((B t)⁻¹ *ᵥ deriv c t)) := by
  obtain ⟨K, hK, hw⟩ := source_horizontal_generator_bound_of_criticality k X hX CX C0 hCX hC0
  refine ⟨K, hK, ?_⟩
  intro R hR F hF c s hs hi hc B₀ hmin
  obtain ⟨a, b, ha, hb, hab, B, hB₀, hsm, hB⟩ :=
    exists_horizontal_minimizingFrame_with_criticality F c hs hi hc
      (sourceRegularization CX C0 R) (sourceRegularization_pos CX C0 R hCX hC0 hR) B₀ hmin
  refine ⟨a, b, ha, hb, hab, B, hB₀, hsm, ?_⟩
  intro t ht
  obtain ⟨hp, hm, S, hd, hcrit⟩ := hB t ht
  refine ⟨hp, hm, S, hd, ?_⟩
  intro hct
  exact hw R hR F hF (c t) hct ⟨B t, hp⟩ hm ((B t)⁻¹ *ᵥ deriv c t) S hcrit

theorem horizontal_generator_eq_zero_of_degree_le_two {k : ℕ} (hk : k ≤ 2)
    (F : CoefficientSpace k) (lam : ℝ) (hlam : 0 < lam) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : Set ℝ} (hs : IsOpen s)
    (hmin : ∀ u ∈ s, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val)
    {t : ℝ} (ht : t ∈ s) (h : PhysicalSpace) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c (B t *ᵥ h) t) (hB : HasDerivAt B (B t * S.val) t) : S = 0 := by
  have he := differentiated_criticality_on_open F lam c B hs hmin ht h S hc hB
  have hempty : Finset.Icc 2 (k - 1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
  rw [hempty, Finset.sum_empty, mul_zero] at he
  by_contra hne
  have hp := symmetricFrameEnergyHessian_pos F (c t) lam hlam ⟨B t, (hmin t ht).1⟩ S hne
  linarith

theorem horizontal_generator_eq_zero_of_stationary_center {k : ℕ}
    (F : CoefficientSpace k) (lam : ℝ) (hlam : 0 < lam) (c : ℝ → PhysicalSpace)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : Set ℝ} (hs : IsOpen s)
    (hmin : ∀ u ∈ s, 0 < (B u).det ∧
      ∀ D : PositiveFrame, FrameEnergy F (c u) lam (B u) ≤ FrameEnergy F (c u) lam D.val)
    {t : ℝ} (ht : t ∈ s) (S : SymmetricMatrix 3)
    (hc : HasDerivAt c 0 t) (hB : HasDerivAt B (B t * S.val) t) : S = 0 := by
  let M := ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F (c t) (B t) r
  have hM : 0 ≤ M := Finset.sum_nonneg (fun r _ => jetTensorHSNorm_nonneg F (c t) (B t) r)
  have hb := horizontal_generator_bound_along_minima F lam hlam c B hs hmin ht 0 S
    (by simpa using hc) hB M hM le_rfl
  have hn : matrixFullHSNorm S.val = 0 := by
    have hz : physicalEuclideanNorm (0 : PhysicalSpace) = 0 := by simp [physicalEuclideanNorm, coordinateL2Norm]
    rw [hz, mul_zero] at hb
    exact le_antisymm hb (matrixFullHSNorm_nonneg S.val)
  exact Subtype.ext ((matrixFullHSNorm_eq_zero_iff S.val).mp hn)

end PaperI
