import PaperILean.OriginalUpperBodyFlow

/-! The literal ordered integrals in I1305. No commuting-generator assumption. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

def originalUpperIntegralOne (b : ℝ → Fin 6 → ℝ) (a t : ℝ) (i : Fin 6) : ℝ :=
  ∫ s in a..t, b s i

def originalUpperIntegralTwo (b : ℝ → Fin 6 → ℝ) (a t : ℝ) (i j : Fin 6) : ℝ :=
  ∫ s in a..t, originalUpperIntegralOne b a s i * b s j

def originalUpperIntegralThree (b : ℝ → Fin 6 → ℝ) (a t : ℝ) (i j l : Fin 6) : ℝ :=
  ∫ s in a..t, originalUpperIntegralTwo b a s i j * b s l

def originalUpperOrderedSignature (b : ℝ → Fin 6 → ℝ) (a t : ℝ) : Fin 6 → ℝ :=
  ![originalUpperIntegralOne b a t 0,
    originalUpperIntegralOne b a t 1 + originalUpperIntegralTwo b a t 0 3,
    originalUpperIntegralOne b a t 2 + originalUpperIntegralTwo b a t 0 4 +
      originalUpperIntegralTwo b a t 1 5 + originalUpperIntegralThree b a t 0 3 5,
    originalUpperIntegralOne b a t 3,
    originalUpperIntegralOne b a t 4 + originalUpperIntegralTwo b a t 3 5,
    originalUpperIntegralOne b a t 5]

theorem originalUpperIntegralOne_continuousOn (b : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hb : ContinuousOn b (uIcc a z)) (i : Fin 6) :
    ContinuousOn (fun t => originalUpperIntegralOne b a t i) (uIcc a z) := by
  exact intervalIntegral.continuousOn_primitive_interval'
    ((continuous_apply i).comp_continuousOn hb).intervalIntegrable left_mem_uIcc

theorem originalUpperIntegralTwo_continuousOn (b : ℝ → Fin 6 → ℝ) (a z : ℝ)
    (hb : ContinuousOn b (uIcc a z)) (i j : Fin 6) :
    ContinuousOn (fun t => originalUpperIntegralTwo b a t i j) (uIcc a z) := by
  exact intervalIntegral.continuousOn_primitive_interval'
    ((originalUpperIntegralOne_continuousOn b a z hb i).mul
      ((continuous_apply j).comp_continuousOn hb)).intervalIntegrable left_mem_uIcc

theorem originalUpperFlow_coordinate_integral
    (g b : ℝ → Fin 6 → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z))
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (i : Fin 6) :
    g z i - g a i = ∫ t in a..z, originalUpperBodyVelocity (g t) (b t) i := by
  have hgc : ContinuousOn g (Icc a z) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hbi (j : Fin 6) : ContinuousOn (fun t => b t j) (Icc a z) := (continuous_apply j).comp_continuousOn hb
  have hgi (j : Fin 6) : ContinuousOn (fun t => g t j) (Icc a z) := (continuous_apply j).comp_continuousOn hgc
  have hvc : ContinuousOn (fun t => originalUpperBodyVelocity (g t) (b t) i) (Icc a z) := by
    fin_cases i
    · exact hbi 0
    · exact (hbi 1).add ((hgi 0).mul (hbi 3))
    · exact ((hbi 2).add ((hgi 0).mul (hbi 4))).add ((hgi 1).mul (hbi 5))
    · exact hbi 3
    · exact (hbi 4).add ((hgi 3).mul (hbi 5))
    · exact hbi 5
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_pi.mp (hg t (by simpa [uIcc_of_le haz] using ht)) i
  · exact (hvc.mono (by rw [uIcc_of_le haz])).intervalIntegrable

theorem originalUpperFlow_ordered_integrals
    (g b : ℝ → Fin 6 → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z)) (hzero : g a = 0)
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t) :
    g z = originalUpperOrderedSignature b a z := by
  have hsub {t : ℝ} (ht : t ∈ Icc a z) : Icc a t ⊆ Icc a z :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hb' : ContinuousOn b (uIcc a z) := by simpa [uIcc_of_le haz] using hb
  have hbi (i : Fin 6) : ContinuousOn (fun t => b t i) (uIcc a z) := (continuous_apply i).comp_continuousOn hb'
  have hc1 (i : Fin 6) := originalUpperIntegralOne_continuousOn b a z hb' i
  have hc2 (i j : Fin 6) := originalUpperIntegralTwo_continuousOn b a z hb' i j
  have hint {t : ℝ} (ht : t ∈ Icc a z) (i : Fin 6) :
      g t i = ∫ s in a..t, originalUpperBodyVelocity (g s) (b s) i := by
    have h := originalUpperFlow_coordinate_integral g b a t ht.1 (hb.mono (hsub ht))
      (fun s hs => hg s (hsub ht hs)) i
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
      rw [he, intervalIntegral.integral_add (hbi 1 |>.mono hrestrict |>.intervalIntegrable)
        ((hc1 0).mul (hbi 3) |>.mono hrestrict |>.intervalIntegrable)]
      rfl
    · rw [hint ht 4]
      change (∫ s in a..t, b s 4 + g s 3 * b s 5) = _
      have he : (∫ s in a..t, b s 4 + g s 3 * b s 5) =
          ∫ s in a..t, b s 4 + originalUpperIntegralOne b a s 3 * b s 5 := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [(hfirst (t := s) (hsub ht (by simpa [uIcc_of_le ht.1] using hs))).2.1]
      rw [he, intervalIntegral.integral_add (hbi 4 |>.mono hrestrict |>.intervalIntegrable)
        ((hc1 3).mul (hbi 5) |>.mono hrestrict |>.intervalIntegrable)]
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
    have h24 := (hbi 2).add ((hc1 0).mul (hbi 4))
    have h245 := h24.add ((hc1 1).mul (hbi 5))
    rw [he, intervalIntegral.integral_add h245.intervalIntegrable
      ((hc2 0 3).mul (hbi 5)).intervalIntegrable,
      intervalIntegral.integral_add h24.intervalIntegrable ((hc1 1).mul (hbi 5)).intervalIntegrable,
      intervalIntegral.integral_add (hbi 2).intervalIntegrable ((hc1 0).mul (hbi 4)).intervalIntegrable]
    rfl
  ext i
  fin_cases i
  · exact (hfirst hz).1
  · exact (hsecond hz).1
  · exact hlast
  · exact (hfirst hz).2.1
  · exact (hsecond hz).2
  · exact (hfirst hz).2.2

theorem originalUpperRelativeFrame_ordered_integrals
    (g b : ℝ → Fin 6 → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z))
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t) :
    originalUpperRelativeFrame (g a) (g z) = originalUpperOrderedSignature b a z := by
  exact originalUpperFlow_ordered_integrals _ b a z haz hb
    (originalUpperRelativeFrame_self _) (fun t ht => originalUpperRelativeFrame_hasDerivAt g (g a) (b t) t (hg t ht))

end PaperI
