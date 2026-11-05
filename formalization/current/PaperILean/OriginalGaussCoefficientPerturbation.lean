import PaperILean.OriginalAffinePerturbationBounds
import PaperILean.OriginalQuadraticGaussCoefficients

/-! The original complete coefficient perturbation on a prescribed real
quadratic Gauss box, measured at any fixed anchor frame. Absolute coordinates
and initial shear do not enter the bound. No perturbed root is assumed. -/
noncomputable section
namespace PaperI
open Matrix

theorem originalUpperCoefficientPullback_sub {k : ℕ} (F G : CoefficientSpace k)
    (g : Fin 6 → ℝ) :
    originalUpperCoefficientPullback (F-G) g =
      originalUpperCoefficientPullback F g-originalUpperCoefficientPullback G g :=
  map_sub (affineCoefficientMap k ![g 2,g 4,g 5] (originalUpperLinearMatrix g)) F G

theorem originalUpperCoefficientPullback_comp {k : ℕ} (F : CoefficientSpace k)
    (g h : Fin 6 → ℝ) :
    originalUpperCoefficientPullback (originalUpperCoefficientPullback F g) h =
      originalUpperCoefficientPullback F (originalUpperAffineComp g h) := by
  apply coefficient_ext
  intro x
  simp only [originalUpperCoefficientPullback_phase]
  have hc : originalUpperAffineEval g ![h 2,h 4,h 5] =
      ![(originalUpperAffineComp g h) 2,(originalUpperAffineComp g h) 4,
        (originalUpperAffineComp g h) 5] := by
    ext i
    fin_cases i <;> simp [originalUpperAffineEval,originalUpperAffineComp] <;> ring
  rw [hc,originalUpperAffineEval_comp]
  ring

theorem originalUpperCoefficientPullback_relative {k : ℕ} (F : CoefficientSpace k)
    (g h : Fin 6 → ℝ) :
    originalUpperCoefficientPullback (originalUpperCoefficientPullback F g)
      (originalUpperRelativeFrame g h) = originalUpperCoefficientPullback F h := by
  rw [originalUpperCoefficientPullback_comp,originalUpperRelativeFrame,
    ← originalUpperAffineComp_assoc,(originalUpperAffineComp_inv g).2]
  have hz : originalUpperAffineComp 0 h = h := by
    ext i
    fin_cases i <;> simp [originalUpperAffineComp]
  rw [hz]

theorem originalUpperCoefficient_polynomial_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T : ℝ), 0 ≤ T → ∀ (F : CoefficientSpace k) (g : Fin 6 → ℝ),
      ‖g‖ ≤ T → coefficientEuclideanNorm (originalUpperCoefficientPullback F g) ≤
        C * (3*(1+T))^(2*k) * coefficientEuclideanNorm F := by
  obtain ⟨C,hC,hbound⟩ := originalAffineCoefficient_polynomial_bound k
  refine ⟨C,hC,?_⟩
  intro T hT F g hg
  have hgi (i : Fin 6) : |g i| ≤ T := by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm g i).trans hg
  have hscale : 1 ≤ 3*(1+T) := by linarith
  have hcenter : physicalEuclideanNorm (![g 2,g 4,g 5] : PhysicalSpace) ≤ 3*(1+T) := by
    have ht := coordinateL2Norm_le_of_component_bound (![g 2,g 4,g 5] : PhysicalSpace) T hT
      (by intro i; fin_cases i <;> simpa using hgi _)
    change physicalEuclideanNorm (![g 2,g 4,g 5] : PhysicalSpace) ≤ _ at ht
    norm_num only [Fintype.card_fin] at ht
    have hs : Real.sqrt 3 ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    exact ht.trans ((mul_le_mul_of_nonneg_right hs hT).trans (by linarith))
  have hA : ∀ i j, |originalUpperLinearMatrix g i j| ≤ 3*(1+T) := by
    intro i j
    have h0 : (0:ℝ) ≤ 3*(1+T) := by linarith
    have ht : T ≤ 3*(1+T) := by linarith
    fin_cases i <;> fin_cases j <;> simp [originalUpperLinearMatrix]
    all_goals first | exact hscale | exact h0 | exact (hgi _).trans ht | positivity
  have h := hbound (3*(1+T)) (3*(1+T)) hscale hscale F _ _ hcenter hA
  calc
    _ ≤ C * (3*(1+T))^k * (3*(1+T))^k * coefficientEuclideanNorm F := h
    _ = _ := by rw [show 2*k=k+k by omega,pow_add]; ring

theorem originalQuadraticGaussFrame_perturbation_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r b v t w η H M : ℝ),
      r ≠ 0 → 1 ≤ H → 0 ≤ M → |b| ≤ H → |v| ≤ H → |r⁻¹| ≤ H →
      ∀ (a q : Fin 2 → ℝ), |q 0-a 0| ≤ M → |q 1-a 1| ≤ M →
      ∀ F G : CoefficientSpace k,
      coefficientEuclideanNorm
        (originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η q)-
         originalUpperCoefficientPullback G (originalQuadraticGaussFrame r b v t w η q)) ≤
      C * (3*(1+2*H^3*(1+M)^2))^(2*k) * coefficientEuclideanNorm
        (originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η a)-
         originalUpperCoefficientPullback G (originalQuadraticGaussFrame r b v t w η a)) := by
  obtain ⟨C,hC,hbound⟩ := originalUpperCoefficient_polynomial_bound k
  refine ⟨C,hC,?_⟩
  intro r b v t w η H M hr hH hM hb hv hri a q hp hz F G
  have hT : 0 ≤ 2*H^3*(1+M)^2 := by positivity
  have hframe := (originalQuadraticGaussFrame_conditioned_box r b v t w η H M
    hr hH hM hb hv hri a q hp hz).1
  have h := hbound _ hT
    (originalUpperCoefficientPullback (F-G) (originalQuadraticGaussFrame r b v t w η a))
    _ hframe
  rw [originalUpperCoefficientPullback_relative] at h
  simpa only [originalUpperCoefficientPullback_sub] using h

theorem originalQuadraticGaussFrame_model_defect_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r b v t w η H M : ℝ),
      r ≠ 0 → 1 ≤ H → 0 ≤ M → |b| ≤ H → |v| ≤ H → |r⁻¹| ≤ H →
      ∀ (a q : Fin 2 → ℝ), |q 0-a 0| ≤ M → |q 1-a 1| ≤ M →
      ∀ (F F₀ : CoefficientSpace k) (f : ℝ → ℝ) (lam mu K δ : ℝ),
      (∀ x : Fin 3 → ℝ, phase F₀ x =
        f (originalQuadraticInvariant r b v t w x)+lam*x 1+mu*x 2+K) →
      coefficientEuclideanNorm
        (originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η a)-
         originalUpperCoefficientPullback F₀ (originalQuadraticGaussFrame r b v t w η a)) ≤ δ →
      coefficientEuclideanNorm
        (originalUpperCoefficientPullback F (originalQuadraticGaussFrame r b v t w η q)-
         originalUpperCoefficientPullback F₀ (originalQuadraticGaussFrame r b v t w η a)) ≤
        C * (3*(1+2*H^3*(1+M)^2))^(2*k) * δ := by
  obtain ⟨C,hC,hbound⟩ := originalQuadraticGaussFrame_perturbation_bound k
  refine ⟨C,hC,?_⟩
  intro r b v t w η H M hr hH hM hb hv hri a q hp hz F F₀ f lam mu K δ hF₀ hδ
  rw [originalQuadraticGaussFrame_coefficients_constant F₀ f r b v t w η lam mu K hr hF₀ a q]
  exact (hbound r b v t w η H M hr hH hM hb hv hri a q hp hz F F₀).trans
    (mul_le_mul_of_nonneg_left hδ (by positivity))

end PaperI
