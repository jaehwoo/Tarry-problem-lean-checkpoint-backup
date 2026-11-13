import PaperILean.RegularCoefficientInjectivePartition
import PaperILean.FiniteMultiplicityMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Set MeasureTheory Filter
open scoped ENNReal

namespace PaperI.AffineArea

abbrev Plane := Fin 2 → ℝ

/-- Integrate the actual absolute Jacobian by countably many injective
pieces. The zero-Jacobian part contributes zero, so the cardinality
bound only concerns regular preimages. -/
theorem integral_abs_det_le_mul_volume
    (f : Plane → Plane) (U E Q : Set Plane) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (hQ : MeasurableSet Q) (himage : MapsTo f E Q) (N : ℕ)
    (hN : ∀ y, {x | x ∈ E ∧ (fderiv ℝ f x).det ≠ 0 ∧ f x = y}.encard ≤ N) :
    (∫⁻ x in E, ENNReal.ofReal |(fderiv ℝ f x).det|) ≤ (N : ℝ≥0∞) * volume Q := by
  classical
  let S := {x | x ∈ E ∧ (fderiv ℝ f x).det ≠ 0}
  have hSE : S ⊆ E := fun _ hx => hx.1
  have hcont : ContinuousOn (fun x => (fderiv ℝ f x).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hS : MeasurableSet S := by
    have hop := hcont.isOpen_inter_preimage hU (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
    have heq : S = E ∩ (U ∩ (fun x => (fderiv ℝ f x).det) ⁻¹' {0}ᶜ) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hEU hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    rw [heq]
    exact hE.inter hop.measurableSet
  have hder : ∀ x ∈ S, HasFDerivAt f (fderiv ℝ f x) x := by
    intro x hx
    exact ((hf.contDiffAt (hU.mem_nhds (hEU hx.1))).differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨pieces, hm, hd, hcover, hinj⟩ :=
    exists_measurable_injective_partition_of_det_ne_zero
      f S hS (fderiv ℝ f) hder (fun _ hx => hx.2)
  have hsub : ∀ i, pieces i ⊆ S := by
    intro i
    rw [← hcover]
    exact subset_iUnion pieces i
  have hcount (y : Plane) :
      Finite {x | x ∈ S ∧ f x = y} ∧ Nat.card {x | x ∈ S ∧ f x = y} ≤ N := by
    have hc : {x | x ∈ S ∧ f x = y}.encard ≤ N := by
      simpa only [S, mem_setOf_eq, and_assoc] using hN y
    have hfin := Set.finite_of_encard_le_coe hc
    refine ⟨hfin.to_subtype, ?_⟩
    exact (ENat.toNat_le_toNat hc (by simp)).trans_eq (ENat.toNat_coe N)
  calc
    (∫⁻ x in E, ENNReal.ofReal |(fderiv ℝ f x).det|) =
        ∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ f x).det| := by
      rw [← lintegral_indicator hE, ← lintegral_indicator hS]
      congr 1
      ext x
      by_cases hx : x ∈ E
      · by_cases hz : (fderiv ℝ f x).det = 0
        · simp [S, hx, hz]
        · simp [S, hx, hz]
      · simp [S, hx]
    _ = ∑' i, volume (f '' pieces i) := by
      rw [← hcover, Measure.restrict_iUnion hd hm, lintegral_sum_measure]
      congr 1
      funext i
      exact lintegral_abs_det_fderiv_eq_addHaar_image volume (hm i)
        (fun x hx => (hder x (hsub i hx)).hasFDerivWithinAt) (hinj i)
    _ ≤ (N : ℝ≥0∞) * volume Q :=
      tsum_image_measure_le_of_fiber_bound volume f S pieces Q hQ hsub hd
        (fun i => (hm i).image_of_continuousOn_injOn
          (hf.continuousOn.mono (fun _ hx => hEU (hSE (hsub i hx)))) (hinj i))
        (fun i => image_subset_iff.mpr (fun _ hx => himage (hSE (hsub i hx)))) N hcount

end PaperI.AffineArea
