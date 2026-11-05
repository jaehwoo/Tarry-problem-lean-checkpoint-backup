import PaperILean.SectionIntegralStage
import PaperILean.ActualOrderedPathStage
import PaperILean.OriginalUpperIntegralBounds
import PaperILean.FixedDRelativeStage

/-! The moving-section part of I3244[141,217). The actual section, its full
augmented window, and its D-complement pivot produce endpoint relative-frame
bounds. No derivative at an exceptional cut or endpoint is assumed. -/
noncomputable section
open scoped BigOperators
namespace PaperI.SectionIntervalFlow
open Set MeasureTheory RegularSectionDifferential RegularSectionRates

private theorem polynomial_radius_bound (P A L : ℝ) (hP : 2 ≤ P)
    (hA : 0 ≤ A) (hL0 : 0 ≤ L) (hL : L ≤ P^A) :
    L*(1+L)^2 ≤ P^(9*A+8) ∧
      (L*(1+L)^2)*(1+L*(1+L)^2)^2 ≤ P^(9*A+8) := by
  have hp : 0 < P := by linarith
  have hp1 : 1 ≤ P := by linarith
  have hpow : 1 ≤ P^A := Real.one_le_rpow hp1 hA
  have hsum : 1+L ≤ P^(A+1) := by
    rw [Real.rpow_add hp,Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hp.le A)
    nlinarith
  have hR : L*(1+L)^2 ≤ P^(3*A+2) := by
    calc
      _ ≤ P^A*(P^(A+1))^2 :=
        mul_le_mul hL (pow_le_pow_left₀ (by linarith) hsum 2)
          (sq_nonneg _) (Real.rpow_nonneg hp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast (P^(A+1)) 2,← Real.rpow_mul hp.le,
          ← Real.rpow_add hp]
        congr 1
        ring
  have hR0 : 0 ≤ L*(1+L)^2 := mul_nonneg hL0 (sq_nonneg _)
  have hR1 : 1 ≤ P^(3*A+2) := Real.one_le_rpow hp1 (by linarith)
  have hsumR : 1+L*(1+L)^2 ≤ P^(3*A+3) := by
    have heq : 3*A+3 = (3*A+2)+1 := by ring
    rw [heq,Real.rpow_add hp,Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hp.le (3*A+2))
    nlinarith
  constructor
  · exact hR.trans (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · calc
      _ ≤ P^(3*A+2)*(P^(3*A+3))^2 :=
        mul_le_mul hR (pow_le_pow_left₀ (by linarith) hsumR 2)
          (sq_nonneg _) (Real.rpow_nonneg hp.le _)
      _ = _ := by
        rw [← Real.rpow_natCast (P^(3*A+3)) 2,← Real.rpow_mul hp.le,
          ← Real.rpow_add hp]
        congr 1
        ring

/-- Uniform actual section-to-section relative matrix and inverse control.
The larger source interval supplies only interior continuity and a bounded
semialgebraic graph. The actual two endpoints may be exactly distance one. -/
theorem actual_section_interval_relative
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (g : ℝ → Fin 6 → ℝ) (Γ : Set ((Unit ⊕ Fin 6) → ℝ))
      (AΓ : Finset (MvPolynomial (Unit ⊕ Fin 6) ℝ)) (a z x y : ℝ),
      2 ≤ P → ContinuousOn g (Ioo a z) → AΓ.card ≤ s →
      (∀ p ∈ AΓ, p.totalDegree ≤ D) → PolynomialSignDetermined AΓ Γ →
      (∀ t ∈ Ioo a z, ∀ v : Fin 6 → ℝ,
        Sum.elim (fun _ : Unit => t) v ∈ Γ ↔ v = g t) →
      (∀ t ∈ Ioo a z, g t 3 = t) →
      (∀ t ∈ Ioo a z, augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P^Cw) →
      (∀ t ∈ Ioo a z, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) →
      x ∈ Ioo a z → y ∈ Ioo a z → |y-x| ≤ 1 →
      let U := (originalAffineHomogeneousMatrix (g x))⁻¹ *
        originalAffineHomogeneousMatrix (g y)
      matrixFullHSNorm U + matrixFullHSNorm (U⁻¹) ≤
        P^(9*((N : ℝ)+max Cs 0+2*max Cw 0+1)+15) := by
  classical
  obtain ⟨N,hIntegral⟩ := SectionIntegralStage.actual_unit_interval_body_integral_stage
    hCell hHardt hQE hNash hPiece k s D hk
  obtain ⟨K,hCuts⟩ := SectionIntegralReadouts.actual_section_common_subdivision
    hCell hHardt hQE hNash hPiece k s D
  refine ⟨N,?_⟩
  intro P Cs Cw S0 g Γ AΓ a z x y hP hc hcard hdegree hΓ hgraph hd hwindow hpivot hx hy hlen
  let A : ℝ := (N : ℝ)+max Cs 0+2*max Cw 0+1
  let b : ℝ → Fin 6 → ℝ := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
  let w : ℝ → ℝ := fun t => coordinateL2Norm (b t)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpos : 0 < P := by linarith
  have hp1 : 1 ≤ P := by linarith
  have ordered (u v : ℝ) (hu : u ∈ Ioo a z) (hv : v ∈ Ioo a z)
      (huv : u ≤ v) (hl : v-u ≤ 1) :
      ‖originalUpperRelativeFrame (g u) (g v)‖ ≤ P^(9*A+8) ∧
      ‖originalUpperRelativeFrame (g v) (g u)‖ ≤ P^(9*A+8) := by
    have hinside : Icc u v ⊆ Ioo a z := by
      intro t ht
      exact ⟨hu.1.trans_le ht.1,ht.2.trans_lt hv.2⟩
    have hopen : Ioo u v ⊆ Ioo a z := fun t ht => hinside ⟨ht.1.le,ht.2.le⟩
    obtain ⟨C,huC,hvC,hC,hCK,hprops⟩ :=
      hCuts S0 g Γ AΓ a z hcard hdegree hΓ hc hgraph u v huv hinside
    have hcoords : ∀ l ∈ C, ∀ r ∈ C, l < r → (∀ c ∈ C, c ∉ Ioo l r) →
        ∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => g t i) (Ioo l r) ∧
          DerivativeSignOn (fun t => g t i) (Ioo l r) := by
      intro l hlC r hrC hlr hnone i
      simpa only [SectionIntegralReadouts.jointReadout,Sum.elim_inl] using
        hprops l hlC r hrC hlr hnone (Sum.inl i)
    obtain ⟨_hbi,hformula⟩ := ActualOrderedPathStage.actual_body_on_pieces
      g C u v huv huC hvC hC (hc.mono hinside) hcoords
    change originalUpperRelativeFrame (g u) (g v) = originalUpperOrderedSignature b u v at hformula
    obtain ⟨hwi,hL⟩ := hIntegral P Cs Cw S0 g Γ AΓ u v hP huv hl
      (hc.mono hopen) hcard hdegree hΓ (fun t ht => hgraph t (hopen ht))
      (fun t ht => hd t (hopen ht)) (fun t ht => hwindow t (hopen ht))
      (fun t ht => hpivot t (hopen ht))
    have hw : IntervalIntegrable w volume u v :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le huv).mpr hwi
    have hw0 : ∀ t ∈ Icc u v, 0 ≤ w t := fun t _ => coordinateL2Norm_nonneg _
    have hbw : ∀ t ∈ Icc u v, ∀ i : Fin 6, |b t i| ≤ w t :=
      fun t _ i => abs_le_sqrt_sum_sq (b t) i
    let L := ∫ t in u..v, w t
    have hL0 : 0 ≤ L := intervalIntegral.integral_nonneg huv hw0
    have hLbound : L ≤ P^A := by
      simpa only [L,w,b,A,intervalIntegral.integral_of_le huv,
        integral_Ioc_eq_integral_Ioo] using hL
    have hforward : ‖originalUpperRelativeFrame (g u) (g v)‖ ≤ L*(1+L)^2 := by
      rw [hformula]
      exact originalUpperOrderedSignature_norm_bound b w u v huv hw hw0 hbw
    have hback := originalUpperAffineInv_norm_bound
      (originalUpperRelativeFrame (g u) (g v)) (L*(1+L)^2)
      (mul_nonneg hL0 (sq_nonneg _)) hforward
    rw [← originalUpperRelativeFrame_reverse] at hback
    obtain ⟨hR,hInvR⟩ := polynomial_radius_bound P A L hP hA hL0 hLbound
    exact ⟨hforward.trans hR,hback.trans hInvR⟩
  have hpair : ‖originalUpperRelativeFrame (g x) (g y)‖ ≤ P^(9*A+8) ∧
      ‖originalUpperRelativeFrame (g y) (g x)‖ ≤ P^(9*A+8) := by
    by_cases hxy : x ≤ y
    · exact ordered x y hx hy hxy ((le_abs_self (y-x)).trans hlen)
    · have hyx : y ≤ x := le_of_not_ge hxy
      have hl : x-y ≤ 1 := by
        have hh := (neg_le_abs (y-x)).trans hlen
        linarith
      exact (ordered y x hy hx hyx hl).symm
  have hpow1 : 1 ≤ P^(9*A+8) := Real.one_le_rpow hp1 (by linarith)
  have hforward := FixedDRelativeStage.homogeneous_matrix_HS_bound
    (originalUpperRelativeFrame (g x) (g y)) (2*P^(9*A+8)) (by linarith [hpair.1])
  have hback := FixedDRelativeStage.homogeneous_matrix_HS_bound
    (originalUpperRelativeFrame (g y) (g x)) (2*P^(9*A+8)) (by linarith [hpair.2])
  dsimp only
  rw [originalAffineHomogeneousMatrix_relative,originalAffineHomogeneousMatrix_inverse,
    ← originalUpperRelativeFrame_reverse]
  have h64 : (64 : ℝ) ≤ P^(7 : ℝ) := by
    have hn : (64 : ℝ) ≤ P^(7 : ℕ) := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hP 7
      norm_num at hh
      linarith
    exact hn.trans_eq (Real.rpow_natCast P 7).symm
  calc
    _ ≤ 64*P^(9*A+8) := by linarith
    _ ≤ P^(7 : ℝ)*P^(9*A+8) :=
      mul_le_mul_of_nonneg_right h64 (Real.rpow_nonneg hpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hpos]
      congr 1
      dsimp [A]
      ring

end PaperI.SectionIntervalFlow
