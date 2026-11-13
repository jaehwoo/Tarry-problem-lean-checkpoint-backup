import PaperILean.AugmentedOrbitEuclidean
import PaperILean.RectangularSingularValues

/-! I595-607 and I668-693: decreasing singular values of the exact Euclidean
augmented differential and its normal restriction. These pointwise positivity
statements do not assert uniform lower bounds by a power of the stop parameter. -/

noncomputable section
namespace PaperI

def augmentedOrbitSingularValues (k : ℕ) (S : AugmentedState k) : Fin 6 → ℝ :=
  descendingSingularValues (augmentedOrbitMatrix k S)

def normalOrbitSingularValues (k : ℕ) (S : AugmentedState k) : Fin 3 → ℝ :=
  descendingSingularValues (normalOrbitMatrix k S)

theorem augmentedOrbitSingularValues_nonneg {k : ℕ} (S : AugmentedState k)
    (j : Fin 6) : 0 ≤ augmentedOrbitSingularValues k S j :=
  descendingSingularValues_nonneg _ _

theorem normalOrbitSingularValues_nonneg {k : ℕ} (S : AugmentedState k)
    (j : Fin 3) : 0 ≤ normalOrbitSingularValues k S j :=
  descendingSingularValues_nonneg _ _

theorem augmentedOrbitSingularValues_antitone {k : ℕ} (S : AugmentedState k) :
    Antitone (augmentedOrbitSingularValues k S) :=
  descendingSingularValues_antitone _

theorem normalOrbitSingularValues_antitone {k : ℕ} (S : AugmentedState k) :
    Antitone (normalOrbitSingularValues k S) :=
  descendingSingularValues_antitone _

theorem stopped_normalOrbit_last_singularValue_pos {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    0 < normalOrbitSingularValues k S 2 := by
  apply (descendingSingularValues_pos_iff_rank (normalOrbitMatrix k S) 2).mpr
  rw [stopped_normalOrbitMatrix_rank hP S hstop]
  norm_num

theorem stopped_augmentedOrbit_fourth_singularValue_pos {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    0 < augmentedOrbitSingularValues k S 3 := by
  apply (descendingSingularValues_pos_iff_rank (augmentedOrbitMatrix k S) 3).mpr
  have hrank := stopped_augmentedOrbitMatrix_rank_ge_four hP S hstop
  change 3 < (augmentedOrbitMatrix k S).rank
  omega

theorem stopped_normalOrbit_last_singularValue_pos_of_two_le {k : ℕ} {P : ℝ}
    (hP : 2 ≤ P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    0 < normalOrbitSingularValues k S 2 :=
  stopped_normalOrbit_last_singularValue_pos (lt_of_lt_of_le (by norm_num) hP) S hstop

theorem stopped_augmentedOrbit_fourth_singularValue_pos_of_two_le {k : ℕ} {P : ℝ}
    (hP : 2 ≤ P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    0 < augmentedOrbitSingularValues k S 3 :=
  stopped_augmentedOrbit_fourth_singularValue_pos (lt_of_lt_of_le (by norm_num) hP) S hstop

end PaperI
