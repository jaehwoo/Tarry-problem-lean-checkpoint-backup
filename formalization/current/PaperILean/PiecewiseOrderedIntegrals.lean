import PaperILean.FinitePieceFTC
import PaperILean.OriginalUpperOrderedIntegrals

/-! The exact original ordered signature for integrable body velocities,
including singular analytic endpoints and finitely many interior cuts. -/
noncomputable section
namespace PaperI.PiecewiseOrderedIntegrals
open Set MeasureTheory FinitePieceFTC

theorem integralOne_continuous (b : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z) (i : Fin 6) :
    ContinuousOn (fun t => originalUpperIntegralOne b a t i) (uIcc a z) :=
  intervalIntegral.continuousOn_primitive_interval' (hb i) left_mem_uIcc

theorem integralTwo_continuous (b : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z) (i j : Fin 6) :
    ContinuousOn (fun t => originalUpperIntegralTwo b a t i j) (uIcc a z) :=
  intervalIntegral.continuousOn_primitive_interval'
    ((hb j).continuousOn_mul (integralOne_continuous b a z hb i)) left_mem_uIcc

/-- All ordered integrands, including the third level, are genuinely integrable. -/
theorem ordered_integrands_integrable (b : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z) :
    (∀ i j, IntervalIntegrable (fun t => originalUpperIntegralOne b a t i * b t j) volume a z) ∧
    (∀ i j k, IntervalIntegrable (fun t => originalUpperIntegralTwo b a t i j * b t k) volume a z) :=
  ⟨fun i j => (hb j).continuousOn_mul (integralOne_continuous b a z hb i),
   fun i j k => (hb k).continuousOn_mul (integralTwo_continuous b a z hb i j)⟩

theorem coordinate_integral (g b : ℝ → Fin 6 → ℝ) (C : Finset ℝ)
    (a z : ℝ) (haz : a ≤ z) (hc : ContinuousOn g (Icc a z))
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z)
    (hg : ∀ t ∈ Ioo a z, t ∉ C → HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (i : Fin 6) :
    g z i - g a i = ∫ t in a..z, originalUpperBodyVelocity (g t) (b t) i := by
  have hgi (j : Fin 6) : ContinuousOn (fun t => g t j) (uIcc a z) := by
    simpa only [uIcc_of_le haz] using (continuous_apply j).comp_continuousOn hc
  have hi : IntervalIntegrable (fun t => originalUpperBodyVelocity (g t) (b t) i) volume a z := by
    fin_cases i
    · exact hb 0
    · exact (hb 1).add ((hb 3).continuousOn_mul (hgi 0))
    · exact ((hb 2).add ((hb 4).continuousOn_mul (hgi 0))).add
        ((hb 5).continuousOn_mul (hgi 1))
    · exact hb 3
    · exact (hb 4).add ((hb 5).continuousOn_mul (hgi 3))
    · exact hb 5
  exact (integral_eq_sub_off_finset C (fun t => g t i) _ a z haz
    ((continuous_apply i).comp_continuousOn hc) hi
    (fun t ht htC => hasDerivAt_pi.mp (hg t ht htC) i)).symm

theorem flow_ordered_integrals
    (g b : ℝ → Fin 6 → ℝ) (C : Finset ℝ) (a z : ℝ) (haz : a ≤ z)
    (hgc : ContinuousOn g (Icc a z))
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z) (hzero : g a = 0)
    (hg : ∀ t ∈ Ioo a z, t ∉ C → HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t) :
    g z = originalUpperOrderedSignature b a z := by
  have hsub {t : ℝ} (ht : t ∈ Icc a z) : Icc a t ⊆ Icc a z :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hbi := hb
  have hc1 (i : Fin 6) := integralOne_continuous b a z hb i
  have hc2 (i j : Fin 6) := integralTwo_continuous b a z hb i j
  have hint {t : ℝ} (ht : t ∈ Icc a z) (i : Fin 6) :
      g t i = ∫ s in a..t, originalUpperBodyVelocity (g s) (b s) i := by
    have hrestrict : uIcc a t ⊆ uIcc a z := by
      simpa only [uIcc_of_le ht.1,uIcc_of_le haz] using hsub ht
    have h := coordinate_integral g b C a t ht.1 (hgc.mono (hsub ht))
      (fun i => (hb i).mono_set hrestrict)
      (fun s hs hsC => hg s ⟨hs.1,hs.2.trans_le ht.2⟩ hsC) i
    simpa [hzero] using h
  have hfirst {t : ℝ} (ht : t ∈ Icc a z) :
      g t 0 = originalUpperIntegralOne b a t 0 ∧
      g t 3 = originalUpperIntegralOne b a t 3 ∧
      g t 5 = originalUpperIntegralOne b a t 5 := by
    exact ⟨hint ht 0, hint ht 3, hint ht 5⟩
  have hsecond {t : ℝ} (ht : t ∈ Icc a z) :
      g t 1 = originalUpperIntegralOne b a t 1 + originalUpperIntegralTwo b a t 0 3 ∧
      g t 4 = originalUpperIntegralOne b a t 4 + originalUpperIntegralTwo b a t 3 5 := by
    have hrestrict : uIcc a t ⊆ uIcc a z := by
      simpa [uIcc_of_le ht.1, uIcc_of_le haz] using hsub ht
    constructor
    · rw [hint ht 1]
      change (∫ s in a..t, b s 1 + g s 0 * b s 3) = _
      have he : (∫ s in a..t, b s 1 + g s 0 * b s 3) =
          ∫ s in a..t, b s 1 + originalUpperIntegralOne b a s 0 * b s 3 := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [(hfirst (t := s) (hsub ht (by simpa [uIcc_of_le ht.1] using hs))).1]
      rw [he, intervalIntegral.integral_add ((hbi 1).mono_set hrestrict)
        (((hbi 3).continuousOn_mul (hc1 0)).mono_set hrestrict)]
      rfl
    · rw [hint ht 4]
      change (∫ s in a..t, b s 4 + g s 3 * b s 5) = _
      have he : (∫ s in a..t, b s 4 + g s 3 * b s 5) =
          ∫ s in a..t, b s 4 + originalUpperIntegralOne b a s 3 * b s 5 := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [(hfirst (t := s) (hsub ht (by simpa [uIcc_of_le ht.1] using hs))).2.1]
      rw [he, intervalIntegral.integral_add ((hbi 4).mono_set hrestrict)
        (((hbi 5).continuousOn_mul (hc1 3)).mono_set hrestrict)]
      rfl
  have hz : z ∈ Icc a z := ⟨haz, le_rfl⟩
  have hlast : g z 2 = originalUpperIntegralOne b a z 2 + originalUpperIntegralTwo b a z 0 4 +
      originalUpperIntegralTwo b a z 1 5 + originalUpperIntegralThree b a z 0 3 5 := by
    rw [hint hz 2]
    change (∫ s in a..z, b s 2 + g s 0 * b s 4 + g s 1 * b s 5) = _
    have he : (∫ s in a..z, b s 2 + g s 0 * b s 4 + g s 1 * b s 5) =
        ∫ s in a..z, ((b s 2 + originalUpperIntegralOne b a s 0 * b s 4) +
          originalUpperIntegralOne b a s 1 * b s 5) + originalUpperIntegralTwo b a s 0 3 * b s 5 := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc a z := by simpa [uIcc_of_le haz] using hs
      dsimp only
      rw [(hfirst hs').1, (hsecond hs').1]
      ring
    have h24 := (hbi 2).add ((hbi 4).continuousOn_mul (hc1 0))
    have h245 := h24.add ((hbi 5).continuousOn_mul (hc1 1))
    rw [he, intervalIntegral.integral_add h245
      ((hbi 5).continuousOn_mul (hc2 0 3)),
      intervalIntegral.integral_add h24 ((hbi 5).continuousOn_mul (hc1 1)),
      intervalIntegral.integral_add (hbi 2) ((hbi 4).continuousOn_mul (hc1 0))]
    rfl
  ext i
  fin_cases i
  · exact (hfirst hz).1
  · exact (hsecond hz).1
  · exact hlast
  · exact (hfirst hz).2.1
  · exact (hsecond hz).2
  · exact (hfirst hz).2.2

/-- The actual body field is integrable once the actual coordinate derivatives
are integrable; only continuity, not an absolute-frame bound, is used. -/
theorem body_integrable (g d : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hc : ContinuousOn g (uIcc a z))
    (hd : ∀ i, IntervalIntegrable (fun t => d t i) volume a z) :
    ∀ i, IntervalIntegrable (fun t => originalAffineBodyCoordinates (g t) (d t) i) volume a z := by
  have hgi (i : Fin 6) := (continuous_apply i).comp_continuousOn hc
  intro i
  fin_cases i
  · exact hd 0
  · exact (hd 1).sub ((hd 3).continuousOn_mul (hgi 0))
  · exact ((hd 2).sub ((hd 4).continuousOn_mul (hgi 0))).add
      ((hd 5).continuousOn_mul (((hgi 0).mul (hgi 3)).sub (hgi 1)))
  · exact hd 3
  · exact (hd 4).sub ((hd 5).continuousOn_mul (hgi 3))
  · exact hd 5

/-- The relative formula retains all noncommutative ordered terms. -/
theorem relative_ordered_integrals (g b : ℝ → Fin 6 → ℝ) (C : Finset ℝ)
    (a z : ℝ) (haz : a ≤ z) (hc : ContinuousOn g (Icc a z))
    (hb : ∀ i, IntervalIntegrable (fun t => b t i) volume a z)
    (hg : ∀ t ∈ Ioo a z, t ∉ C → HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t) :
    originalUpperRelativeFrame (g a) (g z) = originalUpperOrderedSignature b a z := by
  have hrc : ContinuousOn (fun t => originalUpperRelativeFrame (g a) (g t)) (Icc a z) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv]
      <;> fun_prop
  exact flow_ordered_integrals _ b C a z haz hrc hb (originalUpperRelativeFrame_self _)
    (fun t ht htC => originalUpperRelativeFrame_hasDerivAt g (g a) (b t) t (hg t ht htC))

end PaperI.PiecewiseOrderedIntegrals

