import PaperILean.StoppedNormalColumns
import Mathlib.Data.Matrix.Rank

/-! I693: finite-dimensional range reduction for the three normal columns.
The range identities below are preparatory: the rank-three hypothesis is
explicit and will be discharged using exclusion of the simultaneous kernel pair. -/

noncomputable section
namespace PaperI

theorem normalOrbit_range_le {k : ℕ} (S : AugmentedState k) :
    LinearMap.range (normalOrbitDifferential k S) ≤
      LinearMap.range (augmentedOrbitDifferential k S) :=
  LinearMap.range_comp_le_range _ _

theorem stopped_normalOrbit_finrank {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    Module.finrank ℝ (LinearMap.range (normalOrbitDifferential k S)) = 3 := by
  rw [LinearMap.finrank_range_of_inj (stopped_normalOrbit_injective hP S hstop)]
  simp

theorem stopped_normalOrbit_range_eq_of_finrank_le_three {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (hrank : Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) ≤ 3) :
    LinearMap.range (normalOrbitDifferential k S) =
      LinearMap.range (augmentedOrbitDifferential k S) := by
  apply Submodule.eq_of_le_of_finrank_le (normalOrbit_range_le S)
  rwa [stopped_normalOrbit_finrank hP S hstop]

theorem stopped_exists_normal_kernel_of_finrank_le_three {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (hrank : Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) ≤ 3)
    (ξ : Fin 6 → ℝ) :
    ∃ v : Fin 3 → ℝ, augmentedOrbitDifferential k S (normalCoordinates v + ξ) = 0 := by
  have hx : -(augmentedOrbitDifferential k S ξ) ∈
      LinearMap.range (normalOrbitDifferential k S) := by
    rw [stopped_normalOrbit_range_eq_of_finrank_le_three hP S hstop hrank]
    exact ⟨-ξ, map_neg _ _⟩
  obtain ⟨v, hv⟩ := hx
  refine ⟨v, ?_⟩
  rw [map_add]
  change normalOrbitDifferential k S v + augmentedOrbitDifferential k S ξ = 0
  rw [hv, neg_add_cancel]

theorem augmentedOrbitMatrix_rank_eq {k : ℕ} (S : AugmentedState k) :
    (augmentedOrbitMatrix k S).rank =
      Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) := by
  have heq : (augmentedOrbitMatrix k S).mulVecLin =
      (augmentedStateCoordinates k).toLinearMap.comp (augmentedOrbitDifferential k S) := by
    apply LinearMap.ext
    intro ξ
    exact augmentedOrbitMatrix_mulVec S ξ
  rw [Matrix.rank, heq, LinearMap.range_comp]
  exact (augmentedStateCoordinates k).finrank_map_eq _

end PaperI
