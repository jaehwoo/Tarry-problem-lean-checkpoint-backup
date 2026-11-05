import PaperILean.SectionIntegralCalculus
import PaperILean.SectionIntegralReadouts
import PaperILean.SectionBodyNormStage
import PaperILean.OriginalGaussRelativeFrameIntegration
import PaperILean.OriginalHaarWindowPivot
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory Matrix
namespace PaperI.SectionIntegralStage
open RegularSectionDifferential RegularSectionRates

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

private theorem actual_augmented_derivative_norm_le_sum {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (t : ℝ) (hg : HasDerivAt g (deriv g t) t) :
    augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t) ≤
      ∑ i : AugmentedCoordinateIndex k,
        |deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) i) t| := by
  have hJ := augmentedPullback_hasDerivAt_body S0 g (deriv g t) t hg
  have hq := coordinates_hasDerivAt_body S0 g (deriv g t) t hg
  have hqi (i : AugmentedCoordinateIndex k) :
      deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) i) t =
        (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
          originalAffineBodyCoordinates (g t) (deriv g t)) i :=
    ((hasDerivAt_pi.mp hq) i).deriv
  rw [hJ.deriv]
  calc
    _ = coordinateL2Norm (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
        originalAffineBodyCoordinates (g t) (deriv g t)) :=
      (augmentedOrbitMatrix_norm _ _).symm
    _ ≤ ∑ i : AugmentedCoordinateIndex k,
        |(augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
          originalAffineBodyCoordinates (g t) (deriv g t)) i| :=
      originalHaar_coordinateL2Norm_le_sum_abs _
    _ = _ := by simp only [hqi]

private theorem actual_body_norm_continuousOn (g : ℝ → Fin 6 → ℝ) (U : Set ℝ)
    (hg : AnalyticOnNhd ℝ g U) :
    ContinuousOn (fun t => coordinateL2Norm
      (originalAffineBodyCoordinates (g t) (deriv g t))) U := by
  have hc := originalAffineBodyCoordinates_continuousOn g (deriv g) U
    hg.continuousOn hg.deriv.continuousOn
  have hn : Continuous (fun v : Fin 6 → ℝ => coordinateL2Norm v) := by
    unfold coordinateL2Norm
    fun_prop
  exact hn.comp_continuousOn hc

private theorem nat_succ_le_rpow (P : ℝ) (hP : 2 ≤ P) (n : ℕ) :
    (n : ℝ)+1 ≤ P^(n : ℝ) := by
  have hpos : 0 < P := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,Real.rpow_add hpos,Real.rpow_one]
    have hp := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hpos.le (n : ℝ))
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith

private theorem unit_integral_power_absorption (N K m : ℕ) (P Cs Cw L : ℝ)
    (hP : 2 ≤ P) (hL : L ≤ 1) :
    P^((N : ℝ)+max Cs 0+max Cw 0+1) *
      (L+2*(K : ℝ)*(m : ℝ)*P^Cw) ≤
        P^(((N+2*K*m : ℕ) : ℝ)+max Cs 0+2*max Cw 0+1) := by
  have hpos : 0 < P := by linarith
  have hone : 1 ≤ P := by linarith
  have hww : P^Cw ≤ P^(max Cw 0) :=
    Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hW1 : 1 ≤ P^(max Cw 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hW0 : 0 ≤ P^(max Cw 0) := Real.rpow_nonneg hpos.le _
  have hc : 1+2*(K : ℝ)*(m : ℝ) ≤ P^((2*K*m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,add_comm] using nat_succ_le_rpow P hP (2*K*m)
  have hinner : L+2*(K : ℝ)*(m : ℝ)*P^Cw ≤
      P^((2*K*m : ℕ) : ℝ)*P^(max Cw 0) := by
    calc
      _ ≤ 1+2*(K : ℝ)*(m : ℝ)*P^(max Cw 0) :=
        add_le_add hL (mul_le_mul_of_nonneg_left hww (by positivity))
      _ ≤ (1+2*(K : ℝ)*(m : ℝ))*P^(max Cw 0) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hW0
  calc
    _ ≤ P^((N : ℝ)+max Cs 0+max Cw 0+1) *
        (P^((2*K*m : ℕ) : ℝ)*P^(max Cw 0)) :=
      mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hpos,← Real.rpow_add hpos]
      congr 1
      push_cast
      ring

/-- I3244[45,140): actual regular-section body integrability on a whole open
unit interval. The five existing published inputs remain explicit. The output
exponent precedes all source coefficients, seed, path and endpoints. -/
theorem actual_unit_interval_body_integral_stage
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (g : ℝ → Fin 6 → ℝ) (Γ : Set ((Unit ⊕ Fin 6) → ℝ))
      (AΓ : Finset (MvPolynomial (Unit ⊕ Fin 6) ℝ)) (a z : ℝ),
      2 ≤ P → a ≤ z → z-a ≤ 1 →
      ContinuousOn g (Ioo a z) → AΓ.card ≤ s →
      (∀ p ∈ AΓ, p.totalDegree ≤ D) → PolynomialSignDetermined AΓ Γ →
      (∀ t ∈ Ioo a z, ∀ x : Fin 6 → ℝ,
        Sum.elim (fun _ : Unit => t) x ∈ Γ ↔ x = g t) →
      (∀ t ∈ Ioo a z, g t 3 = t) →
      (∀ t ∈ Ioo a z, augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P^Cw) →
      (∀ t ∈ Ioo a z, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) →
      IntegrableOn (fun t => coordinateL2Norm
        (originalAffineBodyCoordinates (g t) (deriv g t))) (Ioo a z) ∧
      (∫ t in Ioo a z, coordinateL2Norm
        (originalAffineBodyCoordinates (g t) (deriv g t))) ≤
          P^((N : ℝ)+max Cs 0+2*max Cw 0+1) := by
  classical
  obtain ⟨N0,hN0⟩ := SectionBodyNormStage.regular_d_section_body_norm_stage k hk
  obtain ⟨K,hK⟩ := SectionIntegralReadouts.actual_section_common_subdivision
    hCell hHardt hQE hNash hPiece k s D
  let m : ℕ := Fintype.card (AugmentedCoordinateIndex k)
  refine ⟨N0+2*K*m,?_⟩
  intro P Cs Cw S0 g Γ AΓ a z hP haz hlen hg hcard hdegree hΓ hgraph hd hwindow hσ
  have hpos : 0 < P := by linarith
  let q : AugmentedCoordinateIndex k → ℝ → ℝ := fun i t =>
    augmentedStateCoordinates k (augmentedPullback S0 (g t)) i
  let f : ℝ → ℝ := fun t => coordinateL2Norm
    (originalAffineBodyCoordinates (g t) (deriv g t))
  let A : ℝ := P^((N0 : ℝ)+max Cs 0+max Cw 0+1)
  have hA : 0 ≤ A := Real.rpow_nonneg hpos.le _
  have hresult : IntegrableOn f (Ioo a z) ∧
      (∫ t in Ioo a z, f t) ≤
        A*((z-a)+2*(K : ℝ)*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)*P^Cw) := by
    apply SectionIntegralCalculus.bounded_sign_family_body_integral q f a z A (P^Cw) K
      haz hA (Real.rpow_nonneg hpos.le _)
    · intro i
      exact SectionIntegralReadouts.jointReadout_continuousOn S0 g (Ioo a z) hg (.inr i)
    · intro i t ht
      exact (abs_le_sqrt_sum_sq (augmentedStateCoordinates k (augmentedPullback S0 (g t))) i).trans
        (hwindow t ht)
    · intro t ht
      exact coordinateL2Norm_nonneg _
    · intro u v huv hinside
      obtain ⟨C,hu,hv,hC,hCcard,hprops⟩ :=
        hK S0 g Γ AΓ a z hcard hdegree hΓ hg hgraph u v huv hinside
      refine ⟨C,hu,hv,hC,hCcard,?_⟩
      intro x hx y hy hxy hno
      have hgAnalytic : AnalyticOnNhd ℝ g (Ioo x y) := by
        apply analyticOnNhd_pi_iff.mpr
        intro i
        exact (hprops x hx y hy hxy hno (.inl i)).1
      refine ⟨?_,actual_body_norm_continuousOn g (Ioo x y) hgAnalytic,?_⟩
      · intro i
        exact hprops x hx y hy hxy hno (.inr i)
      · intro t ht
        have htSource : t ∈ Ioo a z := hinside
          ⟨(hC x hx).1.trans ht.1.le, ht.2.le.trans (hC y hy).2⟩
        have hgd : HasDerivAt g (deriv g t) t := (hgAnalytic t ht).differentiableAt.hasDerivAt
        have hdLocal : ∀ᶠ u in 𝓝 t, g u 3 = u := by
          filter_upwards [Ioo_mem_nhds htSource.1 htSource.2] with u hu
          exact hd u hu
        have hpoint := hN0 P Cs Cw S0 g (deriv g t) t hP hgd hdLocal
          (hwindow t htSource) (hσ t htSource)
        exact hpoint.trans (mul_le_mul_of_nonneg_left
          (add_le_add_left (actual_augmented_derivative_norm_le_sum S0 g t hgd) 1) hA)
  refine ⟨hresult.1,hresult.2.trans ?_⟩
  exact unit_integral_power_absorption N0 K m P Cs Cw (z-a) hP hlen

end PaperI.SectionIntegralStage
