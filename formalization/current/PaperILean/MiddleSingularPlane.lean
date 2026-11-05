import PaperILean.MiddleSingularNorm
import PaperILean.OrderedSingularBasis

/-! I3253[243,368): the actual two-dimensional subspace contracted by B.
It is the image of the first two ordered right-singular directions of M.
No supplied plane, physical invertibility, or rank hypothesis is assumed. -/

noncomputable section
open scoped InnerProductSpace
namespace PaperI.MiddleSingularPlane
open MiddleSingularNorm

noncomputable def topTwoExtension : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun z j := if h : j.val < 2 then z ⟨j.val, h⟩ else 0
  map_add' := by intros; ext j; dsimp; split <;> simp
  map_smul' := by intros; ext j; dsimp; split <;> simp

noncomputable def topTwoEmbedding (M : Matrix (Fin 3) (Fin 4) ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (orderedSingularBasis M).repr.symm.toLinearMap.comp
    ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toLinearMap.comp topTwoExtension)

theorem topTwoEmbedding_coordinate (M : Matrix (Fin 3) (Fin 4) ℝ)
    (z : Fin 2 → ℝ) (j : Fin 4) :
    (orderedSingularBasis M).repr (topTwoEmbedding M z) j =
      if h : j.val < 2 then z ⟨j.val, h⟩ else 0 := by
  simp [topTwoEmbedding, topTwoExtension]

theorem topTwoEmbedding_injective (M : Matrix (Fin 3) (Fin 4) ℝ) :
    Function.Injective (topTwoEmbedding M) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  funext j
  let j' : Fin 4 := ⟨j.val, lt_trans j.isLt (by decide : 2 < 4)⟩
  have hj := topTwoEmbedding_coordinate M z j'
  rw [hz] at hj
  simpa [j', j.isLt] using hj.symm

theorem topTwoEmbedding_tail_zero (M : Matrix (Fin 3) (Fin 4) ℝ)
    (z : Fin 2 → ℝ) (j : Fin 4) (hj : (1 : Fin 4) < j) :
    ⟪orderedSingularBasis M j, topTwoEmbedding M z⟫_ℝ = 0 := by
  rw [← (orderedSingularBasis M).repr_apply_apply, topTwoEmbedding_coordinate]
  have hn : ¬j.val < 2 := by omega
  simp [hn]

theorem topTwoEmbedding_lower (M : Matrix (Fin 3) (Fin 4) ℝ)
    (δ : ℝ) (hσ : δ ≤ descendingSingularValues M (1 : Fin 4))
    (z : Fin 2 → ℝ) :
    δ * ‖topTwoEmbedding M z‖ ≤ ‖Matrix.toEuclideanLin M (topTwoEmbedding M z)‖ := by
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
    (ordered_singular_lower_bound_of_tail_zero M (1 : Fin 4) _
      (topTwoEmbedding_tail_zero M z))

/-- Actual rank-two image plane and its contraction estimate. -/
theorem contraction_plane (B : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Matrix (Fin 3) (Fin 4) ℝ) (δ ε : ℝ) (hδ : 0 < δ)
    (hσ : δ ≤ descendingSingularValues M (1 : Fin 4))
    (hBM : matrixFrobenius (B * M) ≤ ε) :
    ∃ U : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ U = 2 ∧
        ∀ y ∈ U, ‖Matrix.toEuclideanLin B y‖ ≤ (ε / δ) * ‖y‖ := by
  let A : (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (Matrix.toEuclideanLin M).comp (topTwoEmbedding M)
  have hA : Function.Injective A := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have hb := topTwoEmbedding_lower M δ hσ z
    change δ * ‖topTwoEmbedding M z‖ ≤ ‖A z‖ at hb
    rw [hz, norm_zero] at hb
    have hn : ‖topTwoEmbedding M z‖ = 0 := by
      nlinarith [norm_nonneg (topTwoEmbedding M z)]
    apply topTwoEmbedding_injective M
    simpa only [map_zero] using norm_eq_zero.mp hn
  have hd : Module.finrank ℝ (LinearMap.range A) = 2 := by
    rw [LinearMap.finrank_range_of_inj hA]
    simp
  refine ⟨LinearMap.range A, hd, ?_⟩
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  have hε : 0 ≤ ε := (Real.sqrt_nonneg _).trans hBM
  have hb := topTwoEmbedding_lower M δ hσ z
  change δ * ‖topTwoEmbedding M z‖ ≤ ‖A z‖ at hb
  have hn : ‖topTwoEmbedding M z‖ ≤ ‖A z‖ / δ := by
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using hb
  have hup : ‖Matrix.toEuclideanLin B (A z)‖ ≤
      matrixFrobenius (B * M) * ‖topTwoEmbedding M z‖ := by
    change ‖Matrix.toEuclideanLin B (Matrix.toEuclideanLin M (topTwoEmbedding M z))‖ ≤ _
    rw [← toEuclideanLin_mul_apply]
    exact euclidean_mul_norm_le_frobenius (B * M) _
  calc
    ‖Matrix.toEuclideanLin B (A z)‖ ≤
        matrixFrobenius (B * M) * ‖topTwoEmbedding M z‖ := hup
    _ ≤ ε * ‖topTwoEmbedding M z‖ := mul_le_mul_of_nonneg_right hBM (norm_nonneg _)
    _ ≤ ε * (‖A z‖ / δ) := mul_le_mul_of_nonneg_left hn hε
    _ = (ε / δ) * ‖A z‖ := by ring

end PaperI.MiddleSingularPlane
