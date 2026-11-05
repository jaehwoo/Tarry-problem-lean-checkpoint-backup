import PaperILean.RegularSectionRates
import PaperILean.OriginalHaarWindowPivot

/-! Actual fixed-d body control for the relative-map stage I3237[311,365).
The original D component is zero because the actual path has constant d.
The five-column singular bound is applied to the genuine augmented orbit;
no desired coercivity or derivative identity is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
namespace PaperI.FixedDBodyControl
open RegularSectionDifferential RegularSectionRates

/-- A locally constant original d-coordinate has zero actual D body rate. -/
theorem constant_body_D_eq_zero (g : ℝ → Fin 6 → ℝ) (vel : Fin 6 → ℝ)
    (t d0 : ℝ) (hg : HasDerivAt g vel t)
    (hd : ∀ᶠ u in 𝓝 t, g u 3 = d0) :
    originalAffineBodyCoordinates (g t) vel 3 = 0 := by
  have hcoord : HasDerivAt (fun u => g u 3) (vel 3) t :=
    (hasDerivAt_pi.mp hg) 3
  have hzero : HasDerivAt (fun u => g u 3) 0 t :=
    (hasDerivAt_const t d0).congr_of_eventuallyEq hd
  simpa only [originalAffineBodyCoordinates, Matrix.cons_val_succ, Matrix.cons_val_zero]
    using hcoord.unique hzero

/-- Omit precisely the zero D component from the actual six-column action. -/
theorem orbit_matrix_split_zero {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hD : ξ 3 = 0) :
    augmentedOrbitMatrix k S *ᵥ ξ = dComplement S *ᵥ bodyRates ξ := by
  funext i
  change (∑ j : Fin 6, augmentedOrbitMatrix k S i j * ξ j) =
    ∑ j : Fin 5, augmentedOrbitMatrix k S i ((3 : Fin 6).succAbove j) *
      ξ ((3 : Fin 6).succAbove j)
  simpa only [hD, mul_zero, zero_add] using
    (Fin.sum_univ_succAbove (fun j : Fin 6 => augmentedOrbitMatrix k S i j * ξ j)
      (3 : Fin 6))

/-- The full body Euclidean norm equals the five-rate norm when D vanishes. -/
theorem body_norm_eq_rates_zero (ξ : Fin 6 → ℝ) (hD : ξ 3 = 0) :
    coordinateL2Norm ξ = coordinateL2Norm (bodyRates ξ) := by
  have hs : coordinateL2Norm ξ ^ 2 = coordinateL2Norm (bodyRates ξ) ^ 2 := by
    rw [coordinateL2Norm_sq, coordinateL2Norm_sq]
    calc
      (∑ j : Fin 6, ξ j ^ 2) = ξ 3 ^ 2 +
          ∑ j : Fin 5, ξ ((3 : Fin 6).succAbove j) ^ 2 :=
        Fin.sum_univ_succAbove (fun j : Fin 6 => ξ j ^ 2) (3 : Fin 6)
      _ = _ := by rw [hD]; norm_num [bodyRates]
  nlinarith [coordinateL2Norm_nonneg ξ, coordinateL2Norm_nonneg (bodyRates ξ)]

/-- The source five-column singular lower bound controls the genuine full
body vector in the zero-D Lie algebra, for arbitrary real source exponent. -/
theorem zero_D_norm_coercivity {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hD : ξ 3 = 0) (P Cs : ℝ) (hP : 0 < P)
    (hσ : P ^ (-Cs) ≤ descendingSingularValues (dComplement S) (Fin.last 4)) :
    coordinateL2Norm ξ ≤ P ^ Cs * coordinateL2Norm (augmentedOrbitMatrix k S *ᵥ ξ) := by
  have hlow := (le_least_descendingSingularValue_iff (dComplement S) (P ^ (-Cs))).mp
    hσ ((WithLp.linearEquiv 2 ℝ (Fin 5 → ℝ)).symm (bodyRates ξ))
  have hlow' : P ^ (-Cs) * coordinateL2Norm (bodyRates ξ) ≤
      coordinateL2Norm (dComplement S *ᵥ bodyRates ξ) := by
    simpa only [coordinateL2Norm_eq_norm,
      Matrix.toEuclideanLin_apply_piLp_equiv_symm] using hlow
  rw [← orbit_matrix_split_zero S ξ hD, ← body_norm_eq_rates_zero ξ hD] at hlow'
  have h := mul_le_mul_of_nonneg_left hlow' (Real.rpow_nonneg hP.le Cs)
  have hcancel : P ^ Cs * P ^ (-Cs) = 1 := by
    rw [← Real.rpow_add hP]
    simp
  simpa only [← mul_assoc, hcancel, one_mul] using h

/-- Actual constant-d paths satisfy the augmented-coordinate derivative
majorant used on each analytic piece. The D rate and coercivity are derived,
not included as additional hypotheses. -/
theorem fixed_d_body_majorant {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (vel : Fin 6 → ℝ) (t d0 P Cs : ℝ)
    (hP : 0 < P) (hg : HasDerivAt g vel t)
    (hd : ∀ᶠ u in 𝓝 t, g u 3 = d0)
    (hσ : P ^ (-Cs) ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) :
    ∀ i : Fin 6, |originalAffineBodyCoordinates (g t) vel i| ≤
      P ^ Cs * ∑ j : AugmentedCoordinateIndex k,
        |deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) j) t| := by
  have hD := constant_body_D_eq_zero g vel t d0 hg hd
  have hnorm := zero_D_norm_coercivity (augmentedPullback S0 (g t))
    (originalAffineBodyCoordinates (g t) vel) hD P Cs hP hσ
  have hq := coordinates_hasDerivAt_body S0 g vel t hg
  have hqi (j : AugmentedCoordinateIndex k) :
      deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) j) t =
        (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
          originalAffineBodyCoordinates (g t) vel) j :=
    ((hasDerivAt_pi.mp hq) j).deriv
  have hsum : coordinateL2Norm (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
      originalAffineBodyCoordinates (g t) vel) ≤
      ∑ j : AugmentedCoordinateIndex k,
        |deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) j) t| := by
    simpa only [hqi] using originalHaar_coordinateL2Norm_le_sum_abs
      (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
        originalAffineBodyCoordinates (g t) vel)
  intro i
  exact (abs_le_sqrt_sum_sq (originalAffineBodyCoordinates (g t) vel) i).trans
    (hnorm.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hP.le Cs)))

end PaperI.FixedDBodyControl
