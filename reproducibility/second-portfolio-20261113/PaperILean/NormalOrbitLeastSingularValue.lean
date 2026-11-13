import PaperILean.StoppedOrbitSingularValues
import PaperILean.SingularValueEuclideanBounds

/-! I668-683: the last of the three normal singular values is the exact
minimum on the Euclidean unit sphere in the source normal coefficient space.
This identifies the source s_min; no uniform power estimate is claimed. -/

noncomputable section
namespace PaperI

theorem normalOrbit_last_singularValue_mul_norm_le {k : ℕ} (S : AugmentedState k)
    (v : Fin 3 → ℝ) :
    normalOrbitSingularValues k S 2 * coordinateL2Norm v ≤
      augmentedStateNorm (normalOrbitDifferential k S v) := by
  have h := least_descendingSingularValue_mul_norm_le (normalOrbitMatrix k S)
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm v)
  change normalOrbitSingularValues k S 2 *
    ‖(WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm v‖ ≤
      ‖normalOrbitEuclidean k S ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm v)‖ at h
  rw [normalOrbitEuclidean_norm, LinearEquiv.apply_symm_apply] at h
  rwa [coordinateL2Norm_eq_norm]

theorem normalOrbit_last_singularValue_attained {k : ℕ} (S : AugmentedState k) :
    ∃ v : Fin 3 → ℝ, coordinateL2Norm v = 1 ∧
      augmentedStateNorm (normalOrbitDifferential k S v) =
        normalOrbitSingularValues k S 2 := by
  obtain ⟨x, hx, hnorm⟩ := descendingSingularValue_exists_unit_vector (normalOrbitMatrix k S) 2
  refine ⟨(WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) x, ?_, ?_⟩
  · rw [coordinateL2Norm_eq_norm, LinearEquiv.symm_apply_apply]
    exact hx
  · change ‖normalOrbitEuclidean k S x‖ = normalOrbitSingularValues k S 2 at hnorm
    rwa [normalOrbitEuclidean_norm] at hnorm

end PaperI
