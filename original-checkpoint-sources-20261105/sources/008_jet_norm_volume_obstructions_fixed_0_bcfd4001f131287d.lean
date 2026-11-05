import PaperILean.JetWindowVolume
import PaperILean.CompleteJetNormEquivalence
open scoped BigOperators ENNReal
open MeasureTheory
namespace PaperI
-- Empty fibers permit vacuous positive bounds but do not supply a minimizer.
example : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (∅ : Set ℝ), c ≤ x := by
  exact ⟨1, by norm_num, by simp⟩
example : ¬ ∃ x : ℝ, x ∈ (∅ : Set ℝ) := by simp
-- Strict positivity on the noncompact positive half-line does not yield a positive infimum.
example : ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → c ≤ x := by
  rintro ⟨c, hc, h⟩
  have := h (c / 2) (by linarith)
  linarith
-- k=0 has no positive-order tensor slots: it cannot justify three linear coordinates.
example : Fintype.card (Fin 0) = 0 := by simp
-- Zero linear width is retained by the exact containing-box measure, when k>=1.
example (k : ℕ) (hk : 1 ≤ k) (R : ℝ) :
    coefficientMeasure k (jetCoefficientBox k 0 R) = 0 := by
  rw [jetCoefficientBox_measure k hk]
  simp
-- A negative higher-jet budget gives an empty actual jet window.
example (k : ℕ) (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (K M : ℝ) (hM : M < 0) : affineJetWindow k c B K M = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro F hF
  have hz : 0 ≤ ∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r :=
    Finset.sum_nonneg (fun r _ => jetTensorHSNorm_nonneg F c B r)
  have hb := hF.2
  linarith
-- Conditioning is applied only on the explicitly assumed P>=2 range.
example (P : ℝ) (hP : 2 ≤ P) : 0 < P := by linarith
example : ¬ (2 : ℝ) ≤ 1 := by norm_num
-- Coordinate Euclidean norms are not Pi max norms; even (1,1) has norm sqrt 2.
example : Real.sqrt ((1 : ℝ)^2 + 1^2) ≠ 1 := by
  intro h
  have hs := Real.sq_sqrt (show 0 ≤ (1 : ℝ)^2 + 1^2 by norm_num)
  rw [h] at hs
  norm_num at hs
-- Full 9-dimensional coefficient balls scale with K^9, not K^3 (degree k=2).
example : (2 : ℝ)^9 = 512 ∧ (2 : ℝ)^3 = 8 := by norm_num
-- Matrix singularity cannot be dropped from the coefficient change of variables.
example : (0 : Matrix (Fin 3) (Fin 3) ℝ).det = 0 := by simp
end PaperI
