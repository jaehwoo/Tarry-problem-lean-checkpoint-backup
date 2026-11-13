import PaperILean.SimultaneousKernelPair
import PaperILean.AffineNormalPairDegree
import PaperILean.StoppedTranslationNonconstant

/-! Exclusion of the simultaneous augmented-kernel pair at manuscript I693.
The full directional derivative is split into its constant and nonconstant
cases. The physical action, including its constants, is used in the first
case. Neither the physical matrix nor the full orbit map is assumed injective. -/

noncomputable section
open Matrix
namespace PaperI

theorem affineNormalPair_multiplier_zero_implies_linear_zero (v w : Fin 3 → ℝ)
    (h : normalScalarPolynomial w - MvPolynomial.X 2 * normalScalarPolynomial v = 0) :
    v 0 = 0 ∧ v 1 = 0 := by
  have hn : ¬ (v 0 ≠ 0 ∨ v 1 ≠ 0) := by
    intro hv
    have hd := affineNormalPair_multiplier_degree v w hv
    simp [h] at hd
  constructor
  · by_contra hv
    exact hn (Or.inl hv)
  · by_contra hv
    exact hn (Or.inr hv)

theorem stopped_simultaneous_kernel_pair_linear_zero {k : ℕ} {P : ℝ}
    (hP : 0 < P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (v w : Fin 3 → ℝ)
    (hY : augmentedOrbitDifferential k S (pairYCoordinates v) = 0)
    (hZ : augmentedOrbitDifferential k S (pairZCoordinates w) = 0) :
    v 0 = 0 ∧ v 1 = 0 := by
  by_cases hF : ∃ c : ℝ, MvPolynomial.pderiv 0 (coefficientPolynomial S.1) = MvPolynomial.C c
  · obtain ⟨c, hc⟩ := hF
    have hM : (fun i => S.2.2 i 0) ≠ 0 := by
      intro hz
      exact stopped_pderiv_nonconstant hP S hstop 0 hz c hc
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, S.2.2 i 0 ≠ 0 := by
      by_contra! h
      exact hM (funext h)
    have hp := simultaneous_kernel_pair_physical S v w hY hZ i
    have hC : (MvPolynomial.C (S.2.2 i 0) : MvPolynomial (Fin 3) ℝ) ≠ 0 :=
      MvPolynomial.C_ne_zero.mpr hi
    exact affineNormalPair_multiplier_zero_implies_linear_zero v w
      ((mul_eq_zero.mp hp).resolve_right hC)
  · obtain ⟨c0, c1, hc⟩ := simultaneous_kernel_pair_phase S v w hY hZ
    have hn : ¬ (v 0 ≠ 0 ∨ v 1 ≠ 0) := by
      intro hv
      exact affineNormalPair_product_ne_linear v w hv _
        (fun c hc => hF ⟨c, hc⟩) c0 c1 hc
    constructor
    · by_contra hv
      exact hn (Or.inl hv)
    · by_contra hv
      exact hn (Or.inr hv)

theorem stopped_no_simultaneous_kernel_pair {k : ℕ} {P : ℝ}
    (hP : 0 < P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (v w : Fin 3 → ℝ) :
    ¬ (augmentedOrbitDifferential k S (pairYCoordinates v) = 0 ∧
      augmentedOrbitDifferential k S (pairZCoordinates w) = 0) := by
  rintro ⟨hY, hZ⟩
  obtain ⟨hv0, hv1⟩ := stopped_simultaneous_kernel_pair_linear_zero hP S hstop v w hY hZ
  rw [pairYCoordinates_of_constant v hv0 hv1] at hY
  have h := augmentedOrbit_translation_eq_zero hP S hstop ![v 2, 1, 0] hY
  have h1 := congrFun h 1
  norm_num at h1

theorem stopped_no_simultaneous_kernel_pair_of_two_le {k : ℕ} {P : ℝ}
    (hP : 2 ≤ P) (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (v w : Fin 3 → ℝ) :
    ¬ (augmentedOrbitDifferential k S (pairYCoordinates v) = 0 ∧
      augmentedOrbitDifferential k S (pairZCoordinates w) = 0) :=
  stopped_no_simultaneous_kernel_pair (by linarith) S hstop v w

end PaperI
