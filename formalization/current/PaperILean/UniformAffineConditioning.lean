import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.MiddleCutoffAssembly
import PaperILean.AffineConditioningDefinable

/-! I3251[578,732): uniform conditioning of the actual normalized affine field.
The source window and raw stop may have different real exponents. The
semialgebraic argument is carried out in the radius before this rescaling. -/

noncomputable section
open Matrix
namespace PaperI.AffineConditioning

def windowExponent (Cw Cs : ℝ) : ℝ := max 1 (max Cw Cs)

theorem windowExponent_pos (Cw Cs : ℝ) : 0 < windowExponent Cw Cs :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem radius_two_le (P Cw Cs : ℝ) (hP : 2 ≤ P) :
    2 ≤ P ^ windowExponent Cw Cs := by
  have hPone : 1 ≤ P := by linarith
  apply hP.trans
  calc
    P = P ^ (1 : ℝ) := (Real.rpow_one P).symm
    _ ≤ P ^ windowExponent Cw Cs :=
      Real.rpow_le_rpow_of_exponent_le hPone (le_max_left _ _)

/-- Enlarge the source's actual window and raw projected stop to one radius.
No physical invertibility, same-exponent assumption, or power definability is used. -/
theorem raw_stop_standardized {k : ℕ} (P Cw Cs κ : ℝ) (S : AugmentedState k)
    (hP : 2 ≤ P) (hwindow : augmentedStateNorm S ≤ P ^ Cw)
    (hκ : P ^ (-Cs) ≤ κ)
    (hstop : ∀ u : PhysicalSpace,
      κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
        coefficientEuclideanNorm (directionalCoefficientMap k u S.1) ^ 2 +
          physicalEuclideanNorm (S.2.2 *ᵥ u) ^ 2) :
    AugmentedTranslationStopped (P ^ windowExponent Cw Cs) S := by
  have hPone : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hcw : Cw ≤ windowExponent Cw Cs :=
    (le_max_left Cw Cs).trans (le_max_right 1 _)
  have hcs : Cs ≤ windowExponent Cw Cs :=
    (le_max_right Cw Cs).trans (le_max_right 1 _)
  have hrpos : 0 < P ^ windowExponent Cw Cs := Real.rpow_pos_of_pos hPpos _
  have hinv : (P ^ windowExponent Cw Cs)⁻¹ ≤ κ := by
    calc
      (P ^ windowExponent Cw Cs)⁻¹ = P ^ (-windowExponent Cw Cs) :=
        (Real.rpow_neg hPpos.le _).symm
      _ ≤ P ^ (-Cs) := Real.rpow_le_rpow_of_exponent_le hPone (neg_le_neg hcs)
      _ ≤ κ := hκ
  have hκpos : 0 < κ := (Real.rpow_pos_of_pos hPpos (-Cs)).trans_le hκ
  have hsquare : (P ^ windowExponent Cw Cs) ^ (-2 : ℤ) ≤ κ ^ 2 := by
    simp only [_root_.zpow_neg, zpow_ofNat]
    rw [← inv_pow]
    exact (sq_le_sq₀ (inv_nonneg.mpr hrpos.le) hκpos.le).mpr hinv
  exact ⟨hwindow.trans (Real.rpow_le_rpow_of_exponent_le hPone hcw),
    fun u => (mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)).trans (hstop u)⟩

/-- The minimum graph is the actual fixed family, and bounded-parameter
positivity is supplied by compactness rather than assumed from eventual growth. -/
theorem standardized_gap_rpow_lower (hQE : PublishedRealSemialgebraicity)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ (S : AugmentedState k) (f : FieldIndex → ℝ),
        AugmentedTranslationStopped R S → fieldNorm f = 1 →
          R ^ (-C) ≤ gap k S f := by
  obtain ⟨C, hC, hbound⟩ := published_positive_definable_graph_rpow_lower hQE
    (minimum k) (minimum_pos k hk) (bounded_parameter_lower k hk)
    (minimum_graph_definable k)
  exact ⟨C, hC, fun R hR S f hS hf =>
    (hbound R hR).trans (minimum_le k R hR S f hS hf)⟩

/-- The literal uniform maximum and small-action consequence at I3251[578,732).
The exponent precedes the radius, state, raw stopping scale and all twelve
field entries. The only external input is the existing qualitative QE contract. -/
theorem uniform_affine_conditioning_stage (hQE : PublishedRealSemialgebraicity)
    (k : ℕ) (hk : 2 ≤ k) (Cw Cs : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (S : AugmentedState k) (κ : ℝ)
      (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ),
      2 ≤ P → augmentedStateNorm S ≤ P ^ Cw → P ^ (-Cs) ≤ κ →
      (∀ u : PhysicalSpace,
        κ ^ 2 * physicalEuclideanNorm u ^ 2 ≤
          coefficientEuclideanNorm (directionalCoefficientMap k u S.1) ^ 2 +
            physicalEuclideanNorm (S.2.2 *ᵥ u) ^ 2) →
      RankOneAffineMatrix.affineFieldFrobenius b N = 1 →
      P ^ (-C) ≤ max
        (coefficientEuclideanNorm (affineFieldCoefficientMap k b N S.1) +
          physicalAffineNorm (physicalAffineFieldAction S.2 b N))
        (descendingSingularValues (RankOneAffineMatrix.affineFieldMatrix b N) (1 : Fin 4)) ∧
      (coefficientEuclideanNorm (affineFieldCoefficientMap k b N S.1) +
          physicalAffineNorm (physicalAffineFieldAction S.2 b N) < P ^ (-C) / 2 →
        P ^ (-C) ≤ descendingSingularValues
          (RankOneAffineMatrix.affineFieldMatrix b N) (1 : Fin 4)) := by
  obtain ⟨c, hc, hgap⟩ := standardized_gap_rpow_lower hQE k hk
  refine ⟨windowExponent Cw Cs * c, mul_pos (windowExponent_pos Cw Cs) hc, ?_⟩
  intro P S κ b N hP hwindow hκ hstop hunit
  have hPpos : 0 < P := by linarith
  let f : FieldIndex → ℝ :=
    fun ij => RankOneAffineMatrix.affineFieldMatrix b N ij.1 ij.2
  have hf : fieldNorm f = 1 := by
    rw [fieldNorm_eq_frobenius]
    simpa only [f, fieldTranslation_of_matrix, fieldLinear_of_matrix] using hunit
  have hS := raw_stop_standardized P Cw Cs κ S hP hwindow hκ hstop
  have hbound := hgap (P ^ windowExponent Cw Cs) (radius_two_le P Cw Cs hP) S f hS hf
  have hpower : (P ^ windowExponent Cw Cs) ^ (-c) =
      P ^ (-(windowExponent Cw Cs * c)) := by
    rw [← Real.rpow_mul hPpos.le]
    congr 1
    ring
  rw [hpower] at hbound
  have hactual : P ^ (-(windowExponent Cw Cs * c)) ≤ max
      (coefficientEuclideanNorm (affineFieldCoefficientMap k b N S.1) +
        physicalAffineNorm (physicalAffineFieldAction S.2 b N))
      (descendingSingularValues (RankOneAffineMatrix.affineFieldMatrix b N) (1 : Fin 4)) := by
    simpa only [gap, actualAction, f, fieldTranslation_of_matrix,
      fieldLinear_of_matrix, fieldMatrix] using hbound
  exact ⟨hactual, fun hsmall => MiddleCutoffAssembly.singular_lower_of_max_lower
    _ _ _ (Real.rpow_pos_of_pos hPpos _) hactual hsmall⟩

end PaperI.AffineConditioning
