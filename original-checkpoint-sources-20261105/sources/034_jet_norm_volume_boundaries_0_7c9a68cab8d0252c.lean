import PaperILean.OriginalJetWindowVolume
open scoped BigOperators ENNReal
open MeasureTheory
namespace PaperI
-- k=0 reconstruction has no tensor slots; it is still a total, exact construction.
example (F : CoefficientSpace 0) : higherJetCoefficientPart 0 F = F := by
  apply (completeJetSymmetricEquiv 0).injective
  funext r
  exact Fin.elim0 r
-- At k=1, removing the first tensor leaves the zero coefficient vector.
example (F : CoefficientSpace 1) : higherJetCoefficientPart 1 F = 0 := by
  apply (completeJetSymmetricEquiv 1).injective
  change completeJetSymmetricMap 1 (higherJetCoefficientPart 1 F) = completeJetSymmetricMap 1 0
  rw [completeJetSymmetricMap_higherJetCoefficientPart, map_zero]
  funext r
  have hr : r.val = 0 := by omega
  simp [higherSymmetricJetPart, hr]
-- No positive higher budget, no invertibility and no linear bound is needed for the radius implication.
example (k : ℕ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (F : CoefficientSpace k),
    (∑ r ∈ Finset.Icc 2 k, jetTensorHSNorm F c B r ≤ 0) →
      ∀ α : MonomialIndex k, 2 ≤ totalDegree α.val →
        |affineCoefficientMap k c B F α| ≤ R :=
  exists_higherJet_coefficient_radius k 0
-- The actual volume conclusion starts at k=1 and keeps the exact source K>=1.
example (M : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ c : PhysicalSpace,
    ∀ B : Matrix (Fin 3) (Fin 3) ℝ, B.det ≠ 0 → ∀ K : ℝ, 1 ≤ K →
      coefficientMeasure 1 (affineJetWindow 1 c B K M) ≤
        ENNReal.ofReal (C * K^3 * |B.det|^(-(chi 1 : ℝ))) :=
  affineJet_window_volume_original_norm_route 1 (by omega) M
-- A zero linear radius annihilates box volume with the proven three-coordinate count.
example (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 ≤ R) :
    coefficientMeasure k (jetCoefficientBox k 0 R) = 0 := by
  rw [jetCoefficientBox_measure_scaled k hk 0 R (by norm_num) hR]
  simp
-- The full source range k>=2 follows without any new assumption.
example (k : ℕ) (hk : 2 ≤ k) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : PhysicalSpace, ∀ B : Matrix (Fin 3) (Fin 3) ℝ,
      B.det ≠ 0 → ∀ K : ℝ, 1 ≤ K →
        coefficientMeasure k (affineJetWindow k c B K M) ≤
          ENNReal.ofReal (C * K^3 * |B.det|^(-(chi k : ℝ))) :=
  affineJet_window_volume_original_norm_route k (by omega) M
end PaperI
