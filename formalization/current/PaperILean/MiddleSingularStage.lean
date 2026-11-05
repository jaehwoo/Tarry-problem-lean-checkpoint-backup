import PaperILean.MiddleSingularPlane
import PaperILean.MiddleSingularMinMax

/-! I3253[243,420): the actual two-dimensional contraction/min-max stage.
The original-label comparison is explicit. The later H bound remains a
conditional corollary of the prepared estimates, not their construction. -/
noncomputable section
open Matrix
namespace PaperI.MiddleSingularStage
open MiddleSingularNorm MiddleSingularPlane MiddleSingularMinMax RankOneAffineMatrix

/-- Complete local source stage, retaining the original physical matrix and label. -/
theorem middle_singular_stage (k : ℕ) (_hk : 2 ≤ k)
    (ell : PhysicalAffineData) (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ)
    (δ ε K d₂ : ℝ) (hδ : 0 < δ)
    (hσ : δ ≤ descendingSingularValues (affineFieldMatrix b N) (1 : Fin 4))
    (hBM : matrixFrobenius (ell.2 * affineFieldMatrix b N) ≤ ε)
    (hK : 0 ≤ K) (hd₂ : d₂ ≤ K * descendingSingularValues ell.2 (1 : Fin 3)) :
    ∃ U : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ U = 2 ∧
      (∀ y ∈ U, ‖Matrix.toEuclideanLin ell.2 y‖ ≤ (ε / δ) * ‖y‖) ∧
      descendingSingularValues ell.2 (1 : Fin 3) ≤ ε / δ ∧ d₂ ≤ K * ε / δ := by
  obtain ⟨U, hdim, hcontract⟩ := contraction_plane ell.2 (affineFieldMatrix b N) δ ε hδ hσ hBM
  have hprod := middle_singular_mul_le_frobenius ell.2 (affineFieldMatrix b N)
  have hmul : descendingSingularValues ell.2 (1 : Fin 3) * δ ≤ ε :=
    (mul_le_mul_of_nonneg_left hσ (descendingSingularValues_nonneg _ _)).trans (hprod.trans hBM)
  have hmid : descendingSingularValues ell.2 (1 : Fin 3) ≤ ε / δ :=
    (le_div_iff₀ hδ).mpr hmul
  refine ⟨U, hdim, hcontract, hmid, ?_⟩
  simpa only [mul_div_assoc] using hd₂.trans (mul_le_mul_of_nonneg_left hmid hK)

/-- Conditional application to the final H bound. All three quantitative
prepared estimates remain explicit premises; no uniform conditioning is claimed. -/
theorem H_bound_of_prepared_estimates (k : ℕ) (hk : 2 ≤ k)
    (ell : PhysicalAffineData) (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ)
    (P H d₂ C₀ C₁ C₂ : ℝ) (hP : 2 ≤ P) (hH : 0 < H) (hd₂ : 0 < d₂)
    (hσ : P ^ (-C₀) ≤ descendingSingularValues (affineFieldMatrix b N) (1 : Fin 4))
    (hBM : matrixFrobenius (ell.2 * affineFieldMatrix b N) ≤ P ^ C₁ / H)
    (hcompare : d₂ ≤ P ^ C₂ * descendingSingularValues ell.2 (1 : Fin 3)) :
    H ≤ P ^ (C₀ + C₁ + C₂) / d₂ := by
  have hPpos : 0 < P := by linarith
  obtain ⟨U, hdim, hc, hm, hd⟩ := middle_singular_stage k hk ell b N
    (P ^ (-C₀)) (P ^ C₁ / H) (P ^ C₂) d₂ (Real.rpow_pos_of_pos hPpos _) hσ hBM
    (Real.rpow_nonneg hPpos.le _) hcompare
  have hpow : P ^ C₂ * (P ^ C₁ / H) / P ^ (-C₀) = P ^ (C₀ + C₁ + C₂) / H := by
    calc
      P ^ C₂ * (P ^ C₁ / H) / P ^ (-C₀) = (P ^ C₀ * P ^ C₁ * P ^ C₂) / H := by
        rw [Real.rpow_neg hPpos.le, div_inv_eq_mul]
        ring
      _ = _ := by rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
  rw [hpow] at hd
  apply (le_div_iff₀ hd₂).mpr
  simpa only [mul_comm] using (le_div_iff₀ hH).mp hd

end PaperI.MiddleSingularStage
