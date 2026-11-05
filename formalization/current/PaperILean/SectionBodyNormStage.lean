import PaperILean.SectionDColumnBound

/-! I3244[0,44): the complete pointwise regular d-section body norm estimate.
The original local section identity, literal five-column singular bound and
full augmented Euclidean window are retained. The fixed-degree exponent is
chosen before all states, paths and scale parameters. The following integral
and packing sentences are not asserted here. -/

noncomputable section
open scoped BigOperators Topology
open Filter Matrix
namespace PaperI.SectionBodyNormStage
open RegularSectionRates RegularSectionDifferential SectionDColumnBound

/-- Restore the omitted D component in the actual Euclidean body norm. -/
theorem body_norm_le_one_add_rates (ξ : Fin 6 → ℝ) (hD : ξ 3 = 1) :
    coordinateL2Norm ξ ≤ 1 + coordinateL2Norm (bodyRates ξ) := by
  have hs : coordinateL2Norm ξ ^ 2 = 1 + coordinateL2Norm (bodyRates ξ) ^ 2 := by
    rw [coordinateL2Norm_sq, coordinateL2Norm_sq]
    calc
      (∑ j : Fin 6, ξ j ^ 2) = ξ 3 ^ 2 +
          ∑ j : Fin 5, ξ ((3 : Fin 6).succAbove j) ^ 2 :=
        Fin.sum_univ_succAbove (fun j : Fin 6 => ξ j ^ 2) (3 : Fin 6)
      _ = _ := by rw [hD]; norm_num [bodyRates]
  nlinarith [coordinateL2Norm_nonneg ξ, coordinateL2Norm_nonneg (bodyRates ξ)]

/-- The source singular lower bound controls the actual five rates, using
the full augmented action and its actual omitted D column. -/
theorem rates_bound_from_actual_split {k : ℕ} (S : AugmentedState k)
    (ξ : Fin 6 → ℝ) (hD : ξ 3 = 1) (P Cs : ℝ) (hP : 0 < P)
    (hσ : P ^ (-Cs) ≤ descendingSingularValues (dComplement S) (Fin.last 4)) :
    coordinateL2Norm (bodyRates ξ) ≤ P ^ Cs *
      (augmentedStateNorm (augmentedOrbitDifferential k S ξ) +
        coordinateL2Norm (dColumn S)) := by
  have hlow := (le_least_descendingSingularValue_iff (dComplement S) (P ^ (-Cs))).mp
    hσ ((WithLp.linearEquiv 2 ℝ (Fin 5 → ℝ)).symm (bodyRates ξ))
  have hlow' : P ^ (-Cs) * coordinateL2Norm (bodyRates ξ) ≤
      coordinateL2Norm (dComplement S *ᵥ bodyRates ξ) := by
    simpa only [coordinateL2Norm_eq_norm,
      Matrix.toEuclideanLin_apply_piLp_equiv_symm] using hlow
  have he : dComplement S *ᵥ bodyRates ξ =
      augmentedOrbitMatrix k S *ᵥ ξ - dColumn S := by
    rw [orbit_matrix_split S ξ hD]
    abel
  have htri : coordinateL2Norm (dComplement S *ᵥ bodyRates ξ) ≤
      coordinateL2Norm (augmentedOrbitMatrix k S *ᵥ ξ) +
        coordinateL2Norm (dColumn S) := by
    rw [he]
    simp only [coordinateL2Norm_eq_norm, map_sub]
    exact norm_sub_le _ _
  rw [augmentedOrbitMatrix_norm] at htri
  have h := mul_le_mul_of_nonneg_left (hlow'.trans htri) (Real.rpow_nonneg hP.le Cs)
  have hcancel : P ^ Cs * P ^ (-Cs) = 1 := by
    rw [← Real.rpow_add hP]
    simp
  simpa only [← mul_assoc, hcancel, one_mul] using h

/-- Absorb the additive unit component and preserve arbitrary real source
exponents by taking their positive parts only in the resulting upper bound. -/
theorem body_power_absorption (N : ℕ) (P Cs Cw x : ℝ)
    (hP : 2 ≤ P) (hx : 0 ≤ x) :
    1 + P ^ Cs * (x + P ^ ((N : ℝ) + max Cw 0)) ≤
      P ^ ((N : ℝ) + max Cs 0 + max Cw 0 + 1) * (1 + x) := by
  have hpos : 0 < P := by linarith
  have hone : 1 ≤ P := by linarith
  let e : ℝ := (N : ℝ) + max Cs 0 + max Cw 0
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hq : 0 ≤ P ^ e := Real.rpow_nonneg hpos.le _
  have h1 : 1 ≤ P ^ e := Real.one_le_rpow hone he
  have hCs : P ^ Cs ≤ P ^ e := by
    apply Real.rpow_le_rpow_of_exponent_le hone
    dsimp [e]
    have := le_max_left Cs 0
    have := le_max_right Cw 0
    linarith
  have hcross : P ^ Cs * P ^ ((N : ℝ) + max Cw 0) ≤ P ^ e := by
    rw [← Real.rpow_add hpos]
    apply Real.rpow_le_rpow_of_exponent_le hone
    dsimp [e]
    have := le_max_left Cs 0
    linarith
  calc
    _ = 1 + P ^ Cs * x + P ^ Cs * P ^ ((N : ℝ) + max Cw 0) := by ring
    _ ≤ P ^ e + P ^ e * x + P ^ e := by
      exact add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right hCs hx)) hcross
    _ = P ^ e * (2 + x) := by ring
    _ ≤ P ^ e * (2 * (1 + x)) := by
      apply mul_le_mul_of_nonneg_left _ hq
      linarith
    _ ≤ P ^ e * (P * (1 + x)) := by
      apply mul_le_mul_of_nonneg_left _ hq
      exact mul_le_mul_of_nonneg_right hP (by linarith)
    _ = P ^ ((N : ℝ) + max Cs 0 + max Cw 0 + 1) * (1 + x) := by
      change P ^ e * (P * (1 + x)) = P ^ (e + 1) * (1 + x)
      rw [Real.rpow_add hpos e 1, Real.rpow_one]
      ring

noncomputable local instance : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedAddCommGroup
noncomputable local instance : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.normedSpace

/-- Complete I3244[0,44), with the actual original body and actual augmented
path derivative. N depends only on k, before P, both exponents and all path data. -/
theorem regular_d_section_body_norm_stage (k : ℕ) (_hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (g : ℝ → Fin 6 → ℝ) (v : Fin 6 → ℝ) (t : ℝ),
      2 ≤ P → HasDerivAt g v t → (∀ᶠ u in 𝓝 t, g u 3 = u) →
      augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P ^ Cw →
      P ^ (-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 (g t))) (Fin.last 4) →
      coordinateL2Norm (originalAffineBodyCoordinates (g t) v) ≤
        P ^ ((N : ℝ) + max Cs 0 + max Cw 0 + 1) *
          (1 + augmentedStateNorm (deriv (fun u => augmentedPullback S0 (g u)) t)) := by
  obtain ⟨N, hN⟩ := dColumn_window_power_bound k
  refine ⟨N, ?_⟩
  intro P Cs Cw S0 g v t hP hg hd hwindow hσ
  have hpos : 0 < P := by linarith
  have hD := section_body_D_eq_one g v t hg hd
  have hr := rates_bound_from_actual_split (augmentedPullback S0 (g t))
    (originalAffineBodyCoordinates (g t) v) hD P Cs hpos hσ
  have hc := hN P Cw (augmentedPullback S0 (g t)) hP hwindow
  rw [(augmentedPullback_hasDerivAt_body S0 g v t hg).deriv]
  calc
    _ ≤ 1 + coordinateL2Norm (bodyRates (originalAffineBodyCoordinates (g t) v)) :=
      body_norm_le_one_add_rates _ hD
    _ ≤ 1 + P ^ Cs *
        (augmentedStateNorm (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
          (originalAffineBodyCoordinates (g t) v)) + coordinateL2Norm
            (dColumn (augmentedPullback S0 (g t)))) := add_le_add_left hr 1
    _ ≤ 1 + P ^ Cs *
        (augmentedStateNorm (augmentedOrbitDifferential k (augmentedPullback S0 (g t))
          (originalAffineBodyCoordinates (g t) v)) + P ^ ((N : ℝ) + max Cw 0)) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left hc _)
        (Real.rpow_nonneg hpos.le Cs)) 1
    _ ≤ _ := body_power_absorption N P Cs Cw _ hP (augmentedStateNorm_nonneg _)

end PaperI.SectionBodyNormStage
