import PaperILean.UniformAffineConditioning
import PaperILean.MiddleCutoffAssembly

/-! I3247-I3254: the complete middle-cutoff lemma for the original prepared
section. The published input remains explicit. All source window, stop,
two-sided body bounds and three original-label comparisons are retained.
The original labels ascend; the formal singular values descend. -/

noncomputable section
open Matrix
namespace PaperI.OriginalMiddleCutoff
open RegularSectionDifferential RankOneAffineMatrix PreparedBodyNormalization
open MiddleCutoffAssembly

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- Complete original middle-cutoff lemma. Its positive exponent is chosen
before every scale, original label, initial state, curve and evaluation point.
The lower body bound and middle lower-comparison direction suffice for the
proof; the full source hypotheses remain in this public statement. -/
theorem original_middle_cutoff (hQE : PublishedRealSemialgebraicity)
    (k : ℕ) (hk : 2 ≤ k) (Ca Cb Cw Cs Ccompare : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P H : ℝ) (d : Fin 3 → ℝ) (S0 : AugmentedState k)
        (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t κ : ℝ),
      2 ≤ P → 0 < H → 0 < d 0 → Monotone d → d 2 ≤ 1 →
      HasDerivAt g v t →
      augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P ^ Cw →
      P ^ (-Cs) ≤ κ →
      (∀ u : PhysicalSpace,
        κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
          coefficientEuclideanNorm
            (directionalCoefficientMap k u (augmentedPullback S0 (g t)).1) ^ 2 +
          physicalEuclideanNorm ((augmentedPullback S0 (g t)).2.2 *ᵥ u) ^ 2) →
      (P ^ (-Cb) ≤ coordinateL2Norm (originalAffineBodyCoordinates (g t) v) ∧
        coordinateL2Norm (originalAffineBodyCoordinates (g t) v) ≤ P ^ Cb) →
      augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
        P ^ Ca / H →
      (∀ i : Fin 3,
        P ^ (-Ccompare) * d i ≤
            descendingSingularValues (augmentedPullback S0 (g t)).2.2 (Fin.rev i) ∧
          descendingSingularValues (augmentedPullback S0 (g t)).2.2 (Fin.rev i) ≤
            P ^ Ccompare * d i) →
      H ≤ P ^ C / d 1 := by
  obtain ⟨c, hc, hconditioning⟩ :=
    AffineConditioning.uniform_affine_conditioning_stage hQE k hk Cw Cs
  let E : ℝ := max ((Ca + Cb + c + 2) + Cw + Ccompare)
    (c + Ca + Cb + Ccompare)
  refine ⟨max 1 E, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro P H d S0 g v t κ hP hH hd0 hdmono _hdupper hg hwindow hκ hstop
    hbody hprepared hcompare
  have hPpos : 0 < P := by linarith
  have hPone : 1 ≤ P := by linarith
  have hd₂ : 0 < d 1 := hd0.trans_le (hdmono (by decide : (0 : Fin 3) ≤ 1))
  let S : AugmentedState k := augmentedPullback S0 (g t)
  let ξ : Fin 6 → ℝ := originalAffineBodyCoordinates (g t) v
  let η : Fin 6 → ℝ := normalizedBody ξ
  have hξ : 0 < coordinateL2Norm ξ :=
    (Real.rpow_pos_of_pos hPpos (-Cb)).trans_le hbody.1
  have hunit : affineFieldFrobenius (upperAffineFieldTranslation η)
      (upperAffineFieldLinear η) = 1 := normalized_body_matrix_norm ξ hξ
  have hgap : P ^ (-c) ≤ max
      (actionSum (augmentedOrbitDifferential k S η))
      (descendingSingularValues
        (affineFieldMatrix (upperAffineFieldTranslation η) (upperAffineFieldLinear η))
        (1 : Fin 4)) :=
    (hconditioning P S κ (upperAffineFieldTranslation η) (upperAffineFieldLinear η)
      hP hwindow hκ hstop hunit).1
  have hrev : Fin.rev (1 : Fin 3) = 1 := by decide
  have hcmp0 := (hcompare (1 : Fin 3)).1
  rw [hrev] at hcmp0
  have hcmp : d 1 ≤ P ^ Ccompare * descendingSingularValues S.2.2 (1 : Fin 3) := by
    calc
      d 1 = P ^ Ccompare * (P ^ (-Ccompare) * d 1) := by
        rw [← mul_assoc, ← Real.rpow_add hPpos]
        simp
      _ ≤ P ^ Ccompare * descendingSingularValues S.2.2 (1 : Fin 3) :=
        mul_le_mul_of_nonneg_left hcmp0 (Real.rpow_nonneg hPpos.le _)
  have hbound := middle_cutoff_of_max_gap k hk S0 g v t hg
    P H (d 1) Ca Cb c Cw Ccompare hP hH hd₂ hbody.1 hprepared hwindow hcmp hgap
  exact hbound.trans (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hPone (le_max_right 1 E)) hd₂.le)

end PaperI.OriginalMiddleCutoff
