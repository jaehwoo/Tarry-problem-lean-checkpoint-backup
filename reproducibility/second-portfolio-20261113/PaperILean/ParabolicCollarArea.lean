import PaperILean.ParabolicCollarGeometry
import PaperILean.FiniteMultiplicityVolume
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Set MeasureTheory
open scoped ENNReal

namespace PaperI.ParabolicCollar

/-- The literal flux-by-time rectangle for the parabolic collar. -/
def fluxRectangle (a b w : ℝ) : Set Coordinates :=
  {x | x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo (-w) w}

theorem fluxRectangle_measurable (a b w : ℝ) : MeasurableSet (fluxRectangle a b w) :=
  (measurableSet_Ioo.preimage (measurable_pi_apply 0)).inter
    (measurableSet_Ioo.preimage (measurable_pi_apply 1))

theorem fluxRectangle_volume {a b w : ℝ} (hab : a ≤ b) :
    volume (fluxRectangle a b w) = ENNReal.ofReal (2 * w * (b-a)) := by
  have heq : fluxRectangle a b w = univ.pi ![Ioo a b, Ioo (-w) w] := by
    ext x
    simp only [fluxRectangle, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [heq, volume_pi, Measure.pi_pi, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  congr 1
  ring

/-- Actual Lebesgue image area, with each preimage counted in the fiber
bound. It includes the zero-length seed case. -/
theorem flux_rectangle_image_area (f : Coordinates → Coordinates) (a b w : ℝ)
    (hab : a ≤ b) (L : Coordinates → Coordinates →L[ℝ] Coordinates)
    (hL : ∀ x ∈ fluxRectangle a b w, HasFDerivAt f (L x) x)
    (hdet : ∀ x ∈ fluxRectangle a b w, (1/2 : ℝ) ≤ (L x).det ∧ (L x).det ≤ 3/2)
    (N : ℕ) (hN : ∀ y, Finite {x | x ∈ fluxRectangle a b w ∧ f x = y} ∧
      Nat.card {x | x ∈ fluxRectangle a b w ∧ f x = y} ≤ N) :
    MeasurableSet (f '' fluxRectangle a b w) ∧
      volume (fluxRectangle a b w) = ENNReal.ofReal (2*w*(b-a)) ∧
      ENNReal.ofReal (2*w*(b-a)) ≤ (2*(N : ℝ≥0∞)) * volume (f '' fluxRectangle a b w) ∧
      volume (f '' fluxRectangle a b w) ≤ ENNReal.ofReal (3*w*(b-a)) := by
  let S := fluxRectangle a b w
  have hS : MeasurableSet S := fluxRectangle_measurable _ _ _
  have hvol : volume S = ENNReal.ofReal (2*w*(b-a)) := fluxRectangle_volume hab
  obtain ⟨t, ht, hd, hcover, hinj⟩ :=
    exists_measurable_injective_partition_of_det_ne_zero f S hS L hL
      (fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num) (hdet x hx).1))
  have hsub (i : ℕ) : t i ⊆ S := by
    rw [← hcover]
    exact subset_iUnion t i
  have him (i : ℕ) : MeasurableSet (f '' t i) :=
    measurable_image_of_fderivWithin (ht i)
      (fun x hx => (hL x (hsub i hx)).hasFDerivWithinAt) (hinj i)
  have heq : f '' S = ⋃ i, f '' t i := by rw [← hcover, image_iUnion]
  have hQ : MeasurableSet (f '' S) := heq ▸ MeasurableSet.iUnion him
  have hlow := finite_multiplicity_measure_le volume f S (f '' S) hS hQ
    (fun _ hx => mem_image_of_mem f hx) L hL (1/2) (by norm_num)
    (fun x hx => (hdet x hx).1.trans (le_abs_self _)) N hN
  refine ⟨hQ, hvol, ?_, ?_⟩
  · rw [← hvol]
    have hc : (N : ℝ≥0∞) / ENNReal.ofReal (1/2) = 2 * N := by
      have hd' : (ENNReal.ofReal (1/2))⁻¹ = 2 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1/2)]
        norm_num
      rw [div_eq_mul_inv, hd', mul_comm]
    simpa only [hc] using hlow
  · have hupper (i : ℕ) : volume (f '' t i) ≤ ENNReal.ofReal (3/2) * volume (t i) := by
      rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume (ht i)
        (fun x hx => (hL x (hsub i hx)).hasFDerivWithinAt) (hinj i)]
      rw [← setLIntegral_const (t i) _]
      apply setLIntegral_mono' (ht i)
      intro x hx
      have hx' := hdet x (hsub i hx)
      rw [abs_of_nonneg (by linarith)]
      exact ENNReal.ofReal_le_ofReal hx'.2
    calc
      volume (f '' S) ≤ ∑' i, volume (f '' t i) := heq ▸ measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (3/2) * volume (t i) := ENNReal.tsum_le_tsum hupper
      _ = ENNReal.ofReal (3/2) * volume S := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hd ht, hcover]
      _ = _ := by
        rw [hvol, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end PaperI.ParabolicCollar
