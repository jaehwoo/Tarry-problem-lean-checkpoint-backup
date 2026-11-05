import PaperILean.RegularSectionDifferential
import PaperILean.RegularSectionPseudoinverse
import Mathlib.Algebra.BigOperators.Fin

/-! I3239[170,378) and I3240-I3242: the actual five body rates of a
regular d-section. The complete augmented orbit uses the source order
A,C,Tx,D,Ty,Tz. The five-column complement and the body-rate vector omit
exactly D, and the fitted vector uses the literal Gram left pseudoinverse.
The right-hand side contains the actual derivative of the augmented
coordinate path, not a separately assumed rate equation. This local identity
does not construct sections or prove a quantitative variation bound. -/

noncomputable section
open scoped BigOperators Topology
open Filter Matrix

namespace PaperI.RegularSectionRates

open RegularSectionDifferential RegularSectionPseudoinverse

/-- The actual five-column complement, in order A,C,Tx,Ty,Tz. -/
noncomputable def dComplement {k : ℕ} (S : AugmentedState k) :
    Matrix (AugmentedCoordinateIndex k) (Fin 5) ℝ :=
  fun i j => augmentedOrbitMatrix k S i ((3 : Fin 6).succAbove j)

/-- The omitted actual D column of the same augmented orbit matrix. -/
noncomputable def dColumn {k : ℕ} (S : AugmentedState k) : AugmentedCoordinateIndex k → ℝ :=
  fun i => augmentedOrbitMatrix k S i 3

/-- The five actual body components in the same complement order. -/
noncomputable def bodyRates (b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  fun j => b ((3 : Fin 6).succAbove j)

/-- The source's fitted coefficients v=-L_d^+(D Jhat). -/
noncomputable def fittedRates {k : ℕ} (S : AugmentedState k) : Fin 5 → ℝ :=
  -(leftPseudoinverse (dComplement S) *ᵥ dColumn S)

theorem orbit_matrix_split {k : ℕ} (S : AugmentedState k)
    (b : Fin 6 → ℝ) (hD : b 3 = 1) :
    augmentedOrbitMatrix k S *ᵥ b =
      dColumn S + dComplement S *ᵥ bodyRates b := by
  funext i
  change (∑ j : Fin 6, augmentedOrbitMatrix k S i j * b j) =
    augmentedOrbitMatrix k S i 3 +
      ∑ j : Fin 5, augmentedOrbitMatrix k S i ((3 : Fin 6).succAbove j) *
        b ((3 : Fin 6).succAbove j)
  simpa only [hD, mul_one] using
    (Fin.sum_univ_succAbove (fun j : Fin 6 => augmentedOrbitMatrix k S i j * b j)
      (3 : Fin 6))

/-- Split the derivative of the actual augmented coefficient/physical path. -/
theorem coordinates_deriv_split {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ)
    (hg : HasDerivAt g v t) (hd : ∀ᶠ u in 𝓝 t, g u 3 = u) :
    deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u))) t =
      dColumn (augmentedPullback S0 (g t)) +
        dComplement (augmentedPullback S0 (g t)) *ᵥ
          bodyRates (originalAffineBodyCoordinates (g t) v) := by
  rw [(coordinates_hasDerivAt_body S0 g v t hg).deriv]
  exact orbit_matrix_split _ _ (section_body_D_eq_one g v t hg hd)

/-- A positive singular-value lower bound proves, rather than assumes, the
left-inverse identity used in the actual section-rate equation. -/
theorem regular_d_section_rates_of_positive_lower {k : ℕ}
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ)
    (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t)
    (hd : ∀ᶠ u in 𝓝 t, g u 3 = u) (τ : ℝ) (hτ : 0 < τ)
    (hσ : τ ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) :
    originalAffineBodyCoordinates (g t) v 3 = 1 ∧
      bodyRates (originalAffineBodyCoordinates (g t) v) =
        fittedRates (augmentedPullback S0 (g t)) +
          leftPseudoinverse (dComplement (augmentedPullback S0 (g t))) *ᵥ
            deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u))) t := by
  refine ⟨section_body_D_eq_one g v t hg hd, ?_⟩
  have hleft := leftPseudoinverse_mul_of_singular_lower
    (dComplement (augmentedPullback S0 (g t))) τ hτ hσ
  have hsplit := coordinates_deriv_split S0 g v t hg hd
  have h := congrArg
    (fun w => leftPseudoinverse (dComplement (augmentedPullback S0 (g t))) *ᵥ w)
    hsplit
  dsimp only at h
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] at h
  funext j
  have hj := congrFun h j
  simp only [Pi.add_apply] at hj
  change bodyRates (originalAffineBodyCoordinates (g t) v) j =
    -(leftPseudoinverse (dComplement (augmentedPullback S0 (g t))) *ᵥ
      dColumn (augmentedPullback S0 (g t))) j +
      (leftPseudoinverse (dComplement (augmentedPullback S0 (g t))) *ᵥ
        deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u))) t) j
  linarith

/-- Complete source stage I3239[170,378)+I3240-I3242. The source degree
range and literal P^(-C) five-column lower bound are retained. -/
theorem regular_d_section_rates_stage {k : ℕ} (_hk : 2 ≤ k)
    (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ)
    (v : Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g v t)
    (hd : ∀ᶠ u in 𝓝 t, g u 3 = u) (P C : ℝ) (hP : 2 ≤ P)
    (hσ : P ^ (-C) ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) :
    originalAffineBodyCoordinates (g t) v 3 = 1 ∧
      bodyRates (originalAffineBodyCoordinates (g t) v) =
        fittedRates (augmentedPullback S0 (g t)) +
          leftPseudoinverse (dComplement (augmentedPullback S0 (g t))) *ᵥ
            deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u))) t := by
  exact regular_d_section_rates_of_positive_lower S0 g v t hg hd (P ^ (-C))
    (Real.rpow_pos_of_pos (by linarith) _) hσ

end PaperI.RegularSectionRates
