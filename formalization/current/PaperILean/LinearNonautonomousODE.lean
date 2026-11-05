import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact

/-! Global existence on a prescribed compact interval for a continuous linear
nonautonomous ODE. A contracting iterate of the actual integral operator is
used; no time-commutativity or matrix-exponential formula is assumed.
The factorial estimate follows the pinned Picard-Lindelof construction. -/
noncomputable section
open Filter Function Set Metric intervalIntegral MeasureTheory
open MeasureTheory.MeasureSpace (volume)
open scoped Topology NNReal ENNReal Nat Interval

namespace PaperI
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ} (hab : a ≤ b)

def linearODEIntegrand (A : C(Icc a b, E →L[ℝ] E)) (f : C(Icc a b, E))
    (t : ℝ) : E :=
  A (projIcc a b hab t) (f (projIcc a b hab t))

omit [CompleteSpace E] in
theorem continuous_linearODEIntegrand (A : C(Icc a b, E →L[ℝ] E))
    (f : C(Icc a b, E)) : Continuous (linearODEIntegrand hab A f) :=
  (A.continuous.clm_apply f.continuous).comp continuous_projIcc

def linearODENext (A : C(Icc a b, E →L[ℝ] E)) (t₀ : Icc a b) (x₀ : E)
    (f : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => x₀ + ∫ τ in (t₀ : ℝ)..(t : ℝ), linearODEIntegrand hab A f τ,
    continuous_const.add ((continuous_iff_continuousAt.mpr fun t =>
      ((continuous_linearODEIntegrand hab A f).integral_hasStrictDerivAt t₀ t).continuousAt).comp
        continuous_subtype_val)⟩

theorem linearODENext_apply (A : C(Icc a b, E →L[ℝ] E)) (t₀ : Icc a b) (x₀ : E)
    (f : C(Icc a b, E)) (t : Icc a b) :
    linearODENext hab A t₀ x₀ f t =
      x₀ + ∫ τ in (t₀ : ℝ)..(t : ℝ), linearODEIntegrand hab A f τ := rfl

theorem linearODENext_dist_le (A : C(Icc a b, E →L[ℝ] E))
    (t₀ : Icc a b) (x₀ : E) {f g : C(Icc a b, E)} {n : ℕ} {d : ℝ}
    (h : ∀ t, dist (f t) (g t) ≤ (‖A‖ * |t.1 - t₀|) ^ n / n ! * d)
    (t : Icc a b) :
    dist (linearODENext hab A t₀ x₀ f t) (linearODENext hab A t₀ x₀ g t) ≤
      (‖A‖ * |t.1 - t₀|) ^ (n + 1) / (n + 1)! * d := by
  have hf := continuous_linearODEIntegrand hab A f
  have hg := continuous_linearODEIntegrand hab A g
  simp only [dist_eq_norm, linearODENext_apply, add_sub_add_left_eq_sub, ←
    intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    norm_integral_eq_norm_integral_uIoc] at *
  calc
    ‖∫ τ in Ι (t₀ : ℝ) t, linearODEIntegrand hab A f τ - linearODEIntegrand hab A g τ‖ ≤
        ∫ τ in Ι (t₀ : ℝ) t, ‖A‖ * ((‖A‖ * |τ - t₀|) ^ n / n ! * d) := by
      refine norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop)) ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun τ hτ => ?_
      have hm : τ ∈ Icc a b := uIcc_subset_Icc t₀.2 t.2 (Ioc_subset_Icc_self hτ)
      let p : Icc a b := ⟨τ, hm⟩
      have hp : projIcc a b hab τ = p := by
        exact projIcc_of_mem hab hm
      simp only [linearODEIntegrand, hp]
      calc
        ‖A p (f p) - A p (g p)‖ ≤ ‖A p‖ * ‖f p - g p‖ := by
          rw [← map_sub]
          exact (A p).le_opNorm _
        _ ≤ ‖A‖ * ((‖A‖ * |τ - t₀|) ^ n / n ! * d) :=
          mul_le_mul (A.norm_coe_le_norm p) (h p) (norm_nonneg _) (norm_nonneg A)
    _ = (‖A‖ * |t.1 - t₀|) ^ (n + 1) / (n + 1)! * d := by
      simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const, integral_pow_abs_sub_uIoc, div_eq_mul_inv,
        pow_succ' ‖A‖, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv, mul_assoc]

theorem linearODENext_iterate_apply_dist_le (A : C(Icc a b, E →L[ℝ] E))
    (t₀ : Icc a b) (x₀ : E) (f g : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((linearODENext hab A t₀ x₀)^[n] f t) ((linearODENext hab A t₀ x₀)^[n] g t) ≤
      (‖A‖ * |t.1 - t₀|) ^ n / n ! * dist f g := by
  induction n generalizing t with
  | zero =>
    simpa only [iterate_zero, id_eq, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact linearODENext_dist_le hab A t₀ x₀ ih t

theorem linearODENext_iterate_dist_le (A : C(Icc a b, E →L[ℝ] E))
    (t₀ : Icc a b) (x₀ : E) (f g : C(Icc a b, E)) (n : ℕ) :
    dist ((linearODENext hab A t₀ x₀)^[n] f) ((linearODENext hab A t₀ x₀)^[n] g) ≤
      (‖A‖ * max (b - t₀) (t₀ - a)) ^ n / n ! * dist f g := by
  haveI : Nonempty (Icc a b) := ⟨t₀⟩
  apply (ContinuousMap.dist_le_iff_of_nonempty).mpr
  intro t
  refine (linearODENext_iterate_apply_dist_le hab A t₀ x₀ f g n t).trans ?_
  have hm : |(t : ℝ) - t₀| ≤ max (b - t₀) (t₀ - a) := by
    apply abs_le.mpr
    have h₁ := le_max_left (b - (t₀ : ℝ)) (t₀ - a)
    have h₂ := le_max_right (b - (t₀ : ℝ)) (t₀ - a)
    constructor <;> linarith [t.2.1, t.2.2]
  gcongr

theorem exists_linearODENext_fixed (A : C(Icc a b, E →L[ℝ] E))
    (t₀ : Icc a b) (x₀ : E) :
    ∃ f : C(Icc a b, E), linearODENext hab A t₀ x₀ f = f := by
  have hT : 0 ≤ max (b - (t₀ : ℝ)) (t₀ - a) :=
    (sub_nonneg.mpr t₀.2.2).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop
    (‖A‖ * max (b - (t₀ : ℝ)) (t₀ - a))).eventually
      (gt_mem_nhds zero_lt_one)).exists
  have hn : 0 ≤ (‖A‖ * max (b - (t₀ : ℝ)) (t₀ - a)) ^ N / N ! :=
    div_nonneg (pow_nonneg (mul_nonneg (norm_nonneg A) hT) _) (Nat.cast_nonneg _)
  let K : ℝ≥0 := ⟨_, hn⟩
  have hc : ContractingWith K (linearODENext hab A t₀ x₀)^[N] :=
    ⟨hN, LipschitzWith.of_dist_le_mul fun f g => linearODENext_iterate_dist_le hab A t₀ x₀ f g N⟩
  exact ⟨_, hc.isFixedPt_fixedPoint_iterate⟩

include hab in
theorem exists_linearODE_Icc (A : C(Icc a b, E →L[ℝ] E))
    (t₀ : Icc a b) (x₀ : E) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧
      ∀ (t : ℝ) (ht : t ∈ Icc a b), HasDerivWithinAt f (A ⟨t, ht⟩ (f t)) (Icc a b) t := by
  obtain ⟨g, hg⟩ := exists_linearODENext_fixed hab A t₀ x₀
  let f : ℝ → E := fun t => g (projIcc a b hab t)
  have hp : ∀ t : Icc a b, projIcc a b hab t = t := fun t => projIcc_val hab t
  refine ⟨f, ?_, ?_⟩
  · change g (projIcc a b hab t₀) = x₀
    rw [hp, ← hg, linearODENext_apply, integral_same, add_zero]
  · intro t ht
    have hd := ((continuous_linearODEIntegrand hab A g).integral_hasStrictDerivAt t₀ t).hasDerivAt.const_add x₀
    have he : f =ᶠ[𝓝[Icc a b] t]
        (fun u => x₀ + ∫ τ in (t₀ : ℝ)..u, linearODEIntegrand hab A g τ) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change g (projIcc a b hab u) = _
      conv_lhs => rw [← hg, linearODENext_apply, projIcc_of_mem hab hu]
    have hd' := hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he ht
    simpa only [linearODEIntegrand, f, projIcc_of_mem hab ht] using hd'


theorem exists_linearODE_Ioo (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (x₀ : E) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀ t ∈ Ioo a b, HasDerivAt f (A t (f t)) t := by
  let Ac : C(Icc a b, E →L[ℝ] E) := ⟨fun t => A t, continuousOn_iff_continuous_restrict.mp hA⟩
  obtain ⟨f, hf₀, hf⟩ := exists_linearODE_Icc (ht₀.1.le.trans ht₀.2.le)
    Ac ⟨t₀, ht₀.1.le, ht₀.2.le⟩ x₀
  exact ⟨f, hf₀, fun t ht =>
    (hf t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

omit [CompleteSpace E] in
theorem linearODE_unique_Ioo (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {f g : ℝ → E}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (A t (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (A t (g t)) t)
    (he : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  let Ac : C(Icc a b, E →L[ℝ] E) := ⟨fun t => A t, continuousOn_iff_continuous_restrict.mp hA⟩
  have hl : ∀ t ∈ Ioo a b, LipschitzOnWith ‖Ac‖₊ (fun x => A t x) univ := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply (A t).lipschitz.weaken
    exact_mod_cast Ac.norm_coe_le_norm ⟨t, ht.1.le, ht.2.le⟩
  exact ODE_solution_unique_of_mem_Ioo hl ht₀
    (fun t ht => ⟨hf t ht, mem_univ _⟩)
    (fun t ht => ⟨hg t ht, mem_univ _⟩) he

end PaperI

