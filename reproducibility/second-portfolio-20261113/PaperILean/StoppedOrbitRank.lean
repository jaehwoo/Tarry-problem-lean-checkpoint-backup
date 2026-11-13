import PaperILean.NormalColumnRank
import PaperILean.StoppedKernelPair

/-! I693: the qualitative rank-at-least-four conclusion for the actual
augmented orbit differential under the manuscript's augmented translation stop.
This uses the three independent normal columns and exclusion of the simultaneous
kernel pair. No singular-value lower bound is asserted. -/

noncomputable section
namespace PaperI

theorem stopped_augmentedOrbit_finrank_ge_four {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    4 ≤ Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) := by
  by_contra h
  have hrank : Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) ≤ 3 := by
    omega
  obtain ⟨v, hv⟩ := stopped_exists_normal_kernel_of_finrank_le_three hP S hstop hrank
    (Pi.single 4 1)
  obtain ⟨w, hw⟩ := stopped_exists_normal_kernel_of_finrank_le_three hP S hstop hrank
    (Pi.single 3 1)
  exact stopped_no_simultaneous_kernel_pair hP S hstop v w ⟨hv, hw⟩

theorem stopped_augmentedOrbitMatrix_rank_ge_four {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    4 ≤ (augmentedOrbitMatrix k S).rank := by
  rw [augmentedOrbitMatrix_rank_eq]
  exact stopped_augmentedOrbit_finrank_ge_four hP S hstop

theorem stopped_augmentedOrbit_finrank_ge_four_of_two_le {k : ℕ} {P : ℝ} (hP : 2 ≤ P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    4 ≤ Module.finrank ℝ (LinearMap.range (augmentedOrbitDifferential k S)) :=
  stopped_augmentedOrbit_finrank_ge_four (lt_of_lt_of_le (by norm_num) hP) S hstop

theorem stopped_augmentedOrbitMatrix_rank_ge_four_of_two_le {k : ℕ} {P : ℝ} (hP : 2 ≤ P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    4 ≤ (augmentedOrbitMatrix k S).rank :=
  stopped_augmentedOrbitMatrix_rank_ge_four (lt_of_lt_of_le (by norm_num) hP) S hstop

end PaperI
