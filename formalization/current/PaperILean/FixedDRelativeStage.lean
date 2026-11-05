import PaperILean.FixedDComponentBound
import PaperILean.OriginalGaussRelativeFrameIntegration
import PaperILean.SpectralHessianForm

/-! I3237[311,365): actual fixed-d relative homogeneous matrices and inverses.
The six existing accepted published inputs are explicit. The subdivision
constant precedes all original states, polynomial coefficients and scales.
No absolute-frame, endpoint derivative, body-integral, or target bound is assumed. -/
noncomputable section
open scoped BigOperators
namespace PaperI.FixedDRelativeStage
open Set RegularSectionDifferential RegularSectionRates FixedDComponentBound

private theorem nat_le_rpow (P : ℝ) (hP : 2 ≤ P) (n : ℕ) :
    (n : ℝ) ≤ P^(n : ℝ) := by
  have hpos : 0 < P := by linarith
  have h : (n : ℝ)+1 ≤ P^(n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, Real.rpow_add hpos, Real.rpow_one]
      have hp := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hpos.le (n : ℝ))
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  linarith

/-- A uniform explicit power for the saved finite-chain polynomial. -/
theorem relative_matrix_power_budget (m M : ℕ) (P Cs Cw : ℝ) (hP : 2 ≤ P) :
    let L : ℝ := P^Cs * (m : ℝ) * (2*P^Cw)
    32 * (1+2*L*(1+L)^2)^M ≤
      P^((M : ℝ)*(6*(m : ℝ)+3*max Cs 0+3*max Cw 0+4)+5) := by
  dsimp only
  have hpos : 0 < P := by linarith
  have hone : 1 ≤ P := by linarith
  let e : ℝ := 2*(m : ℝ)+max Cs 0+max Cw 0
  let L : ℝ := P^Cs * (m : ℝ) * (2*P^Cw)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hm : 2*(m : ℝ) ≤ P^(2*(m : ℝ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using nat_le_rpow P hP (2*m)
  have hs : P^Cs ≤ P^(max Cs 0) :=
    Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hw : P^Cw ≤ P^(max Cw 0) :=
    Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hL : L ≤ P^e := by
    calc
      _ = (2*(m : ℝ))*P^Cs*P^Cw := by dsimp [L]; ring
      _ ≤ P^(2*(m : ℝ))*P^(max Cs 0)*P^(max Cw 0) :=
        mul_le_mul (mul_le_mul hm hs (Real.rpow_nonneg hpos.le _)
          (Real.rpow_nonneg hpos.le _)) hw (Real.rpow_nonneg hpos.le _)
          (mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _))
      _ = P^e := by rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have he1 : 1 ≤ P^e := Real.one_le_rpow hone he
  have h1L : 1+L ≤ P^(e+1) := by
    rw [Real.rpow_add hpos, Real.rpow_one]
    have hp := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hpos.le e)
    nlinarith only [hL,he1,hp]
  have hR : L*(1+L)^2 ≤ P^(3*e+2) := by
    have hh := mul_le_mul hL (pow_le_pow_left₀ (by linarith : 0 ≤ 1+L) h1L 2)
      (sq_nonneg (1+L)) (Real.rpow_nonneg hpos.le e)
    apply hh.trans_eq
    rw [← Real.rpow_natCast (P^(e+1)) 2, ← Real.rpow_mul hpos.le,
      ← Real.rpow_add hpos]
    congr 1
    ring
  have heR : 1 ≤ P^(3*e+2) := Real.one_le_rpow hone (by linarith)
  have h3 : (3 : ℝ) ≤ P^(2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hbase : 1+2*L*(1+L)^2 ≤ P^(3*e+4) := by
    calc
      _ ≤ 3*P^(3*e+2) := by nlinarith only [hR,heR]
      _ ≤ P^(2 : ℝ)*P^(3*e+2) :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hpos.le _)
      _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring
  have h32nat : (32 : ℝ) ≤ P^(5 : ℕ) := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP 5 using 1 <;> norm_num
  have h32 : (32 : ℝ) ≤ P^(5 : ℝ) := by
    exact h32nat.trans_eq (Real.rpow_natCast P 5).symm
  change 32*(1+2*L*(1+L)^2)^M ≤ _
  calc
    _ ≤ P^(5 : ℝ)*(P^(3*e+4))^M :=
      mul_le_mul h32 (pow_le_pow_left₀ (by positivity) hbase M)
        (by positivity) (Real.rpow_nonneg hpos.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hpos.le, ← Real.rpow_add hpos]
      congr 1
      dsimp [e]
      ring

/-- All sixteen entries, including the identity diagonal, are retained. -/
theorem homogeneous_matrix_HS_bound (g : Fin 6 → ℝ) (T : ℝ)
    (hg : ‖g‖+1 ≤ T) : matrixFullHSNorm (originalAffineHomogeneousMatrix g) ≤ 16*T := by
  unfold matrixFullHSNorm
  calc
    _ ≤ ∑ ij : Fin 4 × Fin 4, |originalAffineHomogeneousMatrix g ij.1 ij.2| :=
      originalHaar_coordinateL2Norm_le_sum_abs _
    _ ≤ ∑ _ij : Fin 4 × Fin 4, T := by
      apply Finset.sum_le_sum
      intro ij _
      exact (originalAffineHomogeneousMatrix_entry_bound g ij.1 ij.2).trans
        (by simpa only [add_comm] using hg)
    _ = _ := by simp

/-- The complete source relative-map and actual inverse bound on a connected
fixed-d fiber. Cs and Cw retain their arbitrary real source ranges. -/
theorem actual_fixed_d_relative_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (_hk : 2 ≤ k) :
    ∃ M : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)) (d0 : ℝ),
      2 ≤ P → A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      (∀ g ∈ E, g 3 = d0) →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P^Cw) →
      (∀ g ∈ E, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ z a b : Fin 6 → ℝ, a ∈ connectedComponentIn E z → b ∈ connectedComponentIn E z →
      let U := (originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b
      originalUpperRelativeFrame a b 3 = 0 ∧
        matrixFullHSNorm U + matrixFullHSNorm (U⁻¹) ≤
          P^((M : ℝ)*(6*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)+
            3*max Cs 0+3*max Cw 0+4)+5) := by
  obtain ⟨M,hM⟩ := fixed_d_component_relative_bound hCell hPath hHardt hQE hNash hPiece k s D
  refine ⟨M,?_⟩
  intro P Cs Cw S0 A E d0 hP hAc hAd hAE hd hwindow hσ z a b ha hb
  dsimp only
  let L : ℝ := P^Cs*(Fintype.card (AugmentedCoordinateIndex k) : ℝ)*(2*P^Cw)
  let T : ℝ := (1+2*L*(1+L)^2)^M
  have hf : ‖originalUpperRelativeFrame a b‖+1 ≤ T :=
    hM P Cs Cw S0 A E d0 hP hAc hAd hAE hd hwindow hσ z a b ha hb
  have hr : ‖originalUpperRelativeFrame b a‖+1 ≤ T :=
    hM P Cs Cw S0 A E d0 hP hAc hAd hAE hd hwindow hσ z b a hb ha
  refine ⟨?_,?_⟩
  · have had := hd a ((connectedComponentIn_subset E z) ha)
    have hbd := hd b ((connectedComponentIn_subset E z) hb)
    simp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv,had,hbd]
  · have hforward := homogeneous_matrix_HS_bound (originalUpperRelativeFrame a b) T hf
    have hreverse := homogeneous_matrix_HS_bound (originalUpperRelativeFrame b a) T hr
    have hU : (originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b =
        originalAffineHomogeneousMatrix (originalUpperRelativeFrame a b) :=
      originalAffineHomogeneousMatrix_relative a b
    have hUi : ((originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b)⁻¹ =
        originalAffineHomogeneousMatrix (originalUpperRelativeFrame b a) := by
      rw [hU,originalAffineHomogeneousMatrix_inverse,← originalUpperRelativeFrame_reverse]
    rw [hUi,hU]
    calc
      _ ≤ 32*T := by linarith only [hforward,hreverse]
      _ ≤ _ := relative_matrix_power_budget (Fintype.card (AugmentedCoordinateIndex k)) M P Cs Cw hP

end PaperI.FixedDRelativeStage
