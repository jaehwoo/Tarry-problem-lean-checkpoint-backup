import PaperILean.ShortHStage
import PaperILean.PreparedBodyNormalization

/-! Conditional all-H assembly for the original middle-cutoff argument.
The source's uniform normalized maximum lower bound remains an explicit premise.
The phase-plus-physical action sum is not identified with the augmented norm. -/
noncomputable section
open Matrix
namespace PaperI.MiddleCutoffAssembly
open PreparedPhysicalNorms PreparedBodyNormalization RegularSectionDifferential
open MiddleSingularNorm RankOneAffineMatrix ShortHStage

def actionSum {k : ℕ} (T : AugmentedState k) : ℝ :=
  coefficientEuclideanNorm T.1 + physicalAffineNorm T.2

theorem actionSum_le_twice_norm {k : ℕ} (T : AugmentedState k) :
    actionSum T ≤ 2 * augmentedStateNorm T := by
  have hp : coefficientEuclideanNorm T.1 ≤ augmentedStateNorm T := by
    apply (sq_le_sq₀ (coefficientEuclideanNorm_nonneg _) (augmentedStateNorm_nonneg _)).mp
    rw [augmentedStateNorm_sq_eq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hf := physicalAffineNorm_le_augmented T
  unfold actionSum
  linarith

/-- The source small-action implication at I3251[655,732), retaining its max bound. -/
theorem singular_lower_of_max_lower (δ Q σ : ℝ) (hδ : 0 < δ)
    (hmax : δ ≤ max Q σ) (hsmall : Q < δ / 2) : δ ≤ σ := by
  by_contra hnot
  have hs : σ < δ := lt_of_not_ge hnot
  have hq : Q < δ := by linarith
  exact (not_lt_of_ge hmax) (max_lt hq hs)

theorem threshold_le_power (P a c : ℝ) (hP : 2 ≤ P) :
    4 * P ^ a / P ^ (-c) ≤ P ^ (a + c + 2) := by
  have hpos : 0 < P := by linarith
  have hfour : (4 : ℝ) ≤ P ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  calc
    4 * P ^ a / P ^ (-c) = 4 * P ^ (a + c) := by
      rw [Real.rpow_neg hpos.le, div_inv_eq_mul, Real.rpow_add hpos]
      ring
    _ ≤ P ^ (a + c) * P ^ (2 : ℝ) := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hpos.le (a + c))
    _ = _ := (Real.rpow_add hpos (a + c) 2).symm

theorem action_small_of_long_H (Q A δ H : ℝ) (hδ : 0 < δ) (hH : 0 < H)
    (hQ : Q ≤ 2 * (A / H)) (hlong : 4 * A / δ < H) : Q < δ / 2 := by
  have hh : 4 * A < H * δ := (div_lt_iff₀ hδ).mp hlong
  apply hQ.trans_lt
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hH).mpr
  nlinarith

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- All positive H are covered. The actual uniform normalized maximum lower bound
is the remaining conditioning premise, with its exponent kept explicit. -/
theorem middle_cutoff_of_max_gap (k : ℕ) (hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (P H d₂ Ca Cb Ccond Cw Ccompare : ℝ)
    (hP : 2 ≤ P) (hH : 0 < H) (hd₂ : 0 < d₂)
    (hbody : P ^ (-Cb) ≤ coordinateL2Norm (originalAffineBodyCoordinates (g t) v))
    (hprepared : augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      P ^ Ca / H)
    (hwindow : augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P ^ Cw)
    (hcompare : d₂ ≤ P ^ Ccompare *
      descendingSingularValues (augmentedPullback S0 (g t)).2.2 (1 : Fin 3))
    (hgap : P ^ (-Ccond) ≤ max
      (actionSum (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (normalizedBody (originalAffineBodyCoordinates (g t) v))))
      (descendingSingularValues
        (affineFieldMatrix
          (upperAffineFieldTranslation (normalizedBody (originalAffineBodyCoordinates (g t) v)))
          (upperAffineFieldLinear (normalizedBody (originalAffineBodyCoordinates (g t) v))))
        (1 : Fin 4))) :
    H ≤ P ^ max ((Ca + Cb + Ccond + 2) + Cw + Ccompare)
      (Ccond + Ca + Cb + Ccompare) / d₂ := by
  have hPone : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  by_cases hshort : H ≤ 4 * P ^ (Ca + Cb) / P ^ (-Ccond)
  · have hp : H ≤ P ^ (Ca + Cb + Ccond + 2) :=
      hshort.trans (threshold_le_power P (Ca + Cb) Ccond hP)
    have hb := short_H_stage k hk (augmentedPullback S0 (g t)) P H d₂
      (Ca + Cb + Ccond + 2) Cw Ccompare hP hH hd₂ hwindow hcompare hp
    exact hb.trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hPone (le_max_left _ _)) hd₂.le)
  · have hn := actual_normalized_body_estimates k hk S0 g v t hg P H Ca Cb
      hP hH hbody hprepared
    have hsum := (actionSum_le_twice_norm
      (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
        (normalizedBody (originalAffineBodyCoordinates (g t) v)))).trans
      (mul_le_mul_of_nonneg_left hn.2.1 (by norm_num : (0 : ℝ) ≤ 2))
    have hsmall := action_small_of_long_H _ (P ^ (Ca + Cb)) (P ^ (-Ccond)) H
      (Real.rpow_pos_of_pos hPpos _) hH hsum (lt_of_not_ge hshort)
    have hσ := singular_lower_of_max_lower _ _ _ (Real.rpow_pos_of_pos hPpos _) hgap hsmall
    have hb := H_bound_of_normalized_conditioning k hk S0 g v t hg
      P H d₂ Ca Cb Ccond Ccompare hP hH hd₂ hbody hprepared hσ hcompare
    exact hb.trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hPone (le_max_right _ _)) hd₂.le)

end PaperI.MiddleCutoffAssembly
