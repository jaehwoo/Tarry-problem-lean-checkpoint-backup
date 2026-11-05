import PaperILean.RegularSectionRates
import PaperILean.AugmentedStoppedTopology
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Auxiliary bound for I3244[0,44). The actual D generator is a fixed
linear map on the complete augmented Euclidean coordinate space. Its norm
depends only on k and is absorbed into a power of P before the state and
window exponent are chosen. The manuscript's augmented norm is unchanged. -/

noncomputable section

namespace PaperI.SectionDColumnBound

open RegularSectionRates

/-- The actual D generator transported to the complete Euclidean coordinates. -/
def dStateEuclidean (k : ℕ) :
    EuclideanSpace ℝ (AugmentedCoordinateIndex k) →L[ℝ]
      EuclideanSpace ℝ (AugmentedCoordinateIndex k) :=
  LinearMap.toContinuousLinearMap
    ((augmentedStateEuclideanCoordinates k).toLinearMap.comp
      ((augmentedOrbitStateMap k (Pi.single (3 : Fin 6) 1)).comp
        (augmentedStateEuclideanCoordinates k).symm.toLinearMap))

theorem dStateEuclidean_apply {k : ℕ} (S : AugmentedState k) :
    dStateEuclidean k (augmentedStateEuclideanCoordinates k S) =
      augmentedStateEuclideanCoordinates k
        (augmentedOrbitDifferential k S (Pi.single (3 : Fin 6) 1)) := by
  change augmentedStateEuclideanCoordinates k
    (augmentedOrbitStateMap k (Pi.single (3 : Fin 6) 1)
      ((augmentedStateEuclideanCoordinates k).symm
        (augmentedStateEuclideanCoordinates k S))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem dColumn_norm_eq {k : ℕ} (S : AugmentedState k) :
    coordinateL2Norm (dColumn S) =
      augmentedStateNorm (augmentedOrbitDifferential k S (Pi.single (3 : Fin 6) 1)) := by
  rfl

theorem dColumn_norm_le {k : ℕ} (S : AugmentedState k) :
    coordinateL2Norm (dColumn S) ≤ ‖dStateEuclidean k‖ * augmentedStateNorm S := by
  rw [dColumn_norm_eq]
  simpa only [dStateEuclidean_apply, augmentedStateEuclideanCoordinates_norm] using
    (dStateEuclidean k).le_opNorm (augmentedStateEuclideanCoordinates k S)

/-- The exponent is chosen for k before P, the real window exponent, or state.
Negative window exponents are allowed; no same-P window is imposed. -/
theorem dColumn_window_power_bound (k : ℕ) :
    ∃ N : ℕ, ∀ (P Cw : ℝ) (S : AugmentedState k),
      2 ≤ P → augmentedStateNorm S ≤ P ^ Cw →
      coordinateL2Norm (dColumn S) ≤ P ^ ((N : ℝ) + max Cw 0) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖dStateEuclidean k‖
    (show (1 : ℝ) < 2 by norm_num)
  refine ⟨N, ?_⟩
  intro P Cw S hP hwindow
  have hPpos : 0 < P := by linarith
  have hPone : 1 ≤ P := by linarith
  have hDP : ‖dStateEuclidean k‖ ≤ P ^ (N : ℝ) := by
    rw [Real.rpow_natCast]
    exact hN.le.trans (pow_le_pow_left₀ (by norm_num) hP N)
  have hS : augmentedStateNorm S ≤ P ^ max Cw 0 :=
    hwindow.trans (Real.rpow_le_rpow_of_exponent_le hPone (le_max_left _ _))
  calc
    coordinateL2Norm (dColumn S) ≤ ‖dStateEuclidean k‖ * augmentedStateNorm S :=
      dColumn_norm_le S
    _ ≤ P ^ (N : ℝ) * P ^ max Cw 0 :=
      mul_le_mul hDP hS (augmentedStateNorm_nonneg S) (Real.rpow_nonneg hPpos.le _)
    _ = P ^ ((N : ℝ) + max Cw 0) := (Real.rpow_add hPpos _ _).symm

end PaperI.SectionDColumnBound
