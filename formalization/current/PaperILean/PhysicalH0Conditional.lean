import PaperILean.PhysicalH0Inverse
import PaperILean.OriginalFrameHaarFiberLiteral
import PaperILean.NullFiberCoordinates

/-! The complete conditional H0 bound at I3350[0,345).
All output preimages are retained. The coefficient-output Jacobian and the
specific original null-pivot application are separate manuscript obligations. -/

noncomputable section
namespace PaperI.PhysicalH0Conditional

open Set MeasureTheory OriginalHaarWindowMeasures OriginalHaarArbitraryPhase
open scoped ENNReal

/-- The actual fixed-frame coefficient polynomial reconstructed from an endpoint J. -/
noncomputable def fixedFrame {k : ℕ} (J : CoefficientSpace k) (η f : ℝ)
    (g : Fin 6 → ℝ) : CoefficientSpace k :=
  originalUpperCoefficientPullback J
    (originalUpperAffineInv (originalUpperAffineComp g (NullFiberCoordinates.seed η f)))

/-- The original fixed window is imposed on that reconstructed polynomial. -/
noncomputable def haarFiber {k : ℕ} (W : Set (CoefficientSpace k))
    (J : CoefficientSpace k) (η f : ℝ) : Set (Fin 6 → ℝ) :=
  {g | g ∈ originalHaarSubgroupSet .H0 ∧ fixedFrame J η f g ∈ W}

/-- The conditional integral includes every slice preimage, not just a chosen branch. -/
noncomputable def conditionalHaarIntegral {k n : ℕ}
    (W S : Set (CoefficientSpace k)) (T : CoefficientSpace k → (Fin n → ℝ))
    (t : Fin n → ℝ) (η f : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' J : CoefficientSpace k,
    if J ∈ S ∧ T J = t then I2385ProductHaar.haar0 (haarFiber W J η f) else 0

/-- The reconstruction is the original coefficient action, not a replacement map. -/
theorem fixedFrame_reconstruction {k : ℕ} (F : CoefficientSpace k)
    (η f : ℝ) (g : Fin 6 → ℝ) :
    fixedFrame (originalUpperCoefficientPullback F
      (originalUpperAffineComp g (NullFiberCoordinates.seed η f))) η f g = F := by
  exact NullFiberCoordinates.coefficient_reconstruction F _

/-- In the source's physical endpoint coordinates this is the saved exact fiber action. -/
theorem fixedFrame_physical_coordinates {k : ℕ} (J : CoefficientSpace k)
    (η f : ℝ) (p : NullFiberCoordinates.Fiber) :
    fixedFrame J η f (NullFiberCoordinates.h0 (NullFiberCoordinates.fiberChange η f p)) =
      originalUpperCoefficientPullback J
        (originalUpperAffineInv (NullFiberCoordinates.assemble η f p)) := by
  rw [fixedFrame, NullFiberCoordinates.factor]

/-- The actual inverse-action fiber is bounded by the precise saved Haar orbit set.
No orbit-volume or pivot inequality is an assumption of this bridge. -/
theorem haarFiber_le_literal_orbit {k : ℕ} (W : Set (CoefficientSpace k))
    (J : CoefficientSpace k) (η f : ℝ) :
    I2385ProductHaar.haar0 (haarFiber W J η f) ≤
      I2385ProductHaar.haar0 {g | g ∈ originalHaarSubgroupSet .H0 ∧
        ∃ F ∈ W, ∀ x : PhysicalSpace,
          phase F x = normalizedAlong (phase J)
            (originalUpperAffineComp (originalUpperAffineInv (NullFiberCoordinates.seed η f)) g) x} := by
  let E : Set (Fin 6 → ℝ) := {g | g ∈ originalHaarSubgroupSet .H0 ∧
    ∃ F ∈ W, ∀ x : PhysicalSpace,
      phase F x = normalizedAlong (phase J)
        (originalUpperAffineComp (originalUpperAffineInv (NullFiberCoordinates.seed η f)) g) x}
  have hsub : haarFiber W J η f ⊆ originalUpperAffineInv ⁻¹' E := by
    intro g hg
    refine ⟨subgroup_inv_mem .H0 g hg.1, fixedFrame J η f g, hg.2, ?_⟩
    intro x
    rw [fixedFrame, PhysicalH0Inverse.inv_comp, phase_pullback_normalized]
  calc
    I2385ProductHaar.haar0 (haarFiber W J η f) ≤
        I2385ProductHaar.haar0 (originalUpperAffineInv ⁻¹' E) := measure_mono hsub
    _ ≤ (Measure.map originalUpperAffineInv I2385ProductHaar.haar0) E :=
      Measure.le_map_apply PhysicalH0Inverse.measurable_inv.aemeasurable E
    _ = I2385ProductHaar.haar0 E := by rw [PhysicalH0Inverse.map_inv_haar0]

/-- Exact full-preimage coverage reduces the conditional integral to a finite sum. -/
theorem conditionalHaarIntegral_eq_sum {k n : ℕ}
    (W S : Set (CoefficientSpace k)) (T : CoefficientSpace k → (Fin n → ℝ))
    (t : Fin n → ℝ) (B : Finset (CoefficientSpace k))
    (hB : ∀ J, J ∈ B ↔ J ∈ S ∧ T J = t) (η f : ℝ) :
    conditionalHaarIntegral W S T t η f =
      ∑ J ∈ B, I2385ProductHaar.haar0 (haarFiber W J η f) := by
  classical
  unfold conditionalHaarIntegral
  rw [tsum_eq_sum (s := B) (fun J hJ => if_neg (fun h => hJ ((hB J).mpr h)))]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [if_pos ((hB J).mp hJ)]

/-- I3350's conditional H0 integral, uniformly before the actual windows, output
map, output, and endpoint coordinates. The six accepted published inputs and
source norm/pivot/multiplicity hypotheses remain explicit. No output-Jacobian
weight, endpoint-curvature bound, or singleton-fiber assumption is introduced. -/
theorem physical_h0_conditional_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D M : ℕ) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : Finset (MvPolynomial (MonomialIndex k) ℝ)) (W : Set (CoefficientSpace k)),
        A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A W →
        ∀ P : ℝ, 2 ≤ P →
        (∀ F ∈ W, coefficientEuclideanNorm F ≤ P^c) →
        (∀ F ∈ W, P^(-c) ≤ originalHaarPhysicalLeastSingularValue .H0 F) →
        ∀ (n : ℕ) (S : Set (CoefficientSpace k))
          (T : CoefficientSpace k → (Fin n → ℝ)) (t : Fin n → ℝ)
          (B : Finset (CoefficientSpace k)),
          (∀ J, J ∈ B ↔ J ∈ S ∧ T J = t) → B.card ≤ M →
          ∀ η f : ℝ, conditionalHaarIntegral W S T t η f ≤ ENNReal.ofReal (P^C) := by
  classical
  obtain ⟨A0,hA0,hbound⟩ := originalFrameHaarFiber_literal
    hCell hPath hHardt hQE hNash hPiece k s D
  obtain ⟨b,hb,hmain⟩ := hbound c
  obtain ⟨N,hN⟩ := exists_nat_ge ((M : ℝ)*A0)
  refine ⟨b + N, add_nonneg hb (by positivity), ?_⟩
  intro A W hAc hAd hAW P hP hnorm hpiv n S T t B hB hcard η f
  have hP0 : 0 < P := by linarith
  have hA0nn : 0 ≤ A0 := le_trans (by norm_num) hA0
  have hpoint (J : CoefficientSpace k) :
      I2385ProductHaar.haar0 (haarFiber W J η f) ≤ ENNReal.ofReal (A0*P^b) := by
    apply (haarFiber_le_literal_orbit W J η f).trans
    exact (hmain .H0 A W hAc hAd hAW P hP hnorm hpiv (phase J)
      (originalUpperAffineInv (NullFiberCoordinates.seed η f))).1
  have hconstant : (M : ℝ)*A0 ≤ P^(N : ℝ) := by
    have htwo : (N : ℝ) ≤ (2 : ℝ)^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
    calc
      (M : ℝ)*A0 ≤ (N : ℝ) := hN
      _ ≤ (2 : ℝ)^N := htwo
      _ ≤ P^N := pow_le_pow_left₀ (by norm_num) hP N
      _ = P^(N : ℝ) := (Real.rpow_natCast P N).symm
  rw [conditionalHaarIntegral_eq_sum W S T t B hB η f]
  calc
    (∑ J ∈ B, I2385ProductHaar.haar0 (haarFiber W J η f)) ≤
        ∑ _J ∈ B, ENNReal.ofReal (A0*P^b) := Finset.sum_le_sum (fun J _ => hpoint J)
    _ = (B.card : ℝ≥0∞)*ENNReal.ofReal (A0*P^b) := by simp
    _ ≤ (M : ℝ≥0∞)*ENNReal.ofReal (A0*P^b) :=
      mul_le_mul_right' (by exact_mod_cast hcard) _
    _ = ENNReal.ofReal (((M : ℝ)*A0)*P^b) := by
      rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (M : ℝ))]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (P^(b+(N : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((M : ℝ)*A0)*P^b ≤ P^(N : ℝ)*P^b :=
          mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hP0.le b)
        _ = P^(b+(N : ℝ)) := by rw [Real.rpow_add hP0]; ring

end PaperI.PhysicalH0Conditional
