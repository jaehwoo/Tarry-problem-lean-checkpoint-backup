import PaperILean.OrderedSingularBasis
import PaperILean.OrthonormalFlagIntersection

/-! I600 and I693: constant-one perturbation and continuity for every entry of
the actual decreasing singular-value list. Zeros and multiplicities are retained. -/
noncomputable section
namespace PaperI
variable {m : Type*} [Fintype m] {n : ℕ}

theorem descendingSingularValue_le_add_opNorm
    (A B : Matrix m (Fin n) ℝ) (i : Fin n) :
    descendingSingularValues A i ≤ descendingSingularValues B i +
      ‖rectangularEuclideanCLM A - rectangularEuclideanCLM B‖ := by
  obtain ⟨x, hx, ha, hb⟩ := orthonormal_flags_intersect
    (orderedSingularBasis A) (orderedSingularBasis B) i
  have hlo := ordered_singular_lower_bound_of_tail_zero A i x ha
  have hup := ordered_singular_upper_bound_of_head_zero B i x hb
  have hop := (rectangularEuclideanCLM A - rectangularEuclideanCLM B).le_opNorm x
  have htri := norm_add_le
    ((rectangularEuclideanCLM A - rectangularEuclideanCLM B) x)
    (rectangularEuclideanCLM B x)
  simp only [ContinuousLinearMap.sub_apply, sub_add_cancel,
    rectangularEuclideanCLM_apply] at htri hop
  apply (mul_le_mul_right (norm_pos_iff.mpr hx)).mp
  nlinarith

theorem abs_descendingSingularValue_sub_le
    (A B : Matrix m (Fin n) ℝ) (i : Fin n) :
    |descendingSingularValues A i - descendingSingularValues B i| ≤
      ‖rectangularEuclideanCLM A - rectangularEuclideanCLM B‖ := by
  have hab := descendingSingularValue_le_add_opNorm A B i
  have hba := descendingSingularValue_le_add_opNorm B A i
  rw [norm_sub_rev] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lipschitz_orderedSingularValue (i : Fin n) :
    LipschitzWith 1 (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ m =>
      descendingSingularValues (rectangularEuclideanCLM.symm T) i) := by
  apply LipschitzWith.of_dist_le_mul
  intro T U
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul,
    LinearEquiv.apply_symm_apply] using
    abs_descendingSingularValue_sub_le (rectangularEuclideanCLM.symm T)
      (rectangularEuclideanCLM.symm U) i

theorem continuous_descendingSingularValue (i : Fin n) :
    Continuous (fun A : Matrix m (Fin n) ℝ => descendingSingularValues A i) := by
  have h := (lipschitz_orderedSingularValue (m := m) i).continuous.comp
    (continuous_rectangularEuclideanCLM (m := m) (n := n))
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h

theorem continuous_descendingSingularValues :
    Continuous (fun A : Matrix m (Fin n) ℝ => descendingSingularValues A) :=
  continuous_pi fun i => continuous_descendingSingularValue i

end PaperI
