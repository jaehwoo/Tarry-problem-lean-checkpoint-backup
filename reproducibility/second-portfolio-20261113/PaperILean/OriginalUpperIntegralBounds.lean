import PaperILean.OriginalUpperOrderedIntegrals

/-! Polynomial relative-frame bounds from the original ordered-integral argument. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

theorem originalUpper_weighted_integral_bound
    (w f : ℝ → ℝ) (a z t K : ℝ) (ht : t ∈ Icc a z) (hK : 0 ≤ K)
    (hw : IntervalIntegrable w volume a z) (hw0 : ∀ s ∈ Icc a z, 0 ≤ w s)
    (hf : ∀ s ∈ Icc a t, |f s| ≤ K * w s) :
    |∫ s in a..t, f s| ≤ K * (∫ s in a..z, w s) := by
  have hsub : uIcc a t ⊆ uIcc a z := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hw' := hw.mono_set hsub
  have hn : 0 ≤ ∫ s in a..t, w s :=
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hw0 s ⟨hs.1, hs.2.trans ht.2⟩)
  have hb : ∀ᵐ s ∂volume.restrict (uIoc a t), ‖f s‖ ≤ K * w s := by
    apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro s hs
    exact hf s (by have hs' := hs; rw [uIoc_of_le ht.1] at hs'; exact ⟨hs'.1.le,hs'.2⟩)
  have h := intervalIntegral.norm_integral_le_of_norm_le hb (hw'.const_mul K)
  have hmono : (∫ s in a..t, w s) ≤ ∫ s in a..z, w s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => hw0 s ⟨hs.1.le, hs.2⟩)) hw
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK hn)] at h
  exact h.trans (mul_le_mul_of_nonneg_left hmono hK)

theorem originalUpper_ordered_integral_bounds
    (b : ℝ → Fin 6 → ℝ) (w : ℝ → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hw : IntervalIntegrable w volume a z) (hw0 : ∀ s ∈ Icc a z, 0 ≤ w s)
    (hb : ∀ s ∈ Icc a z, ∀ i : Fin 6, |b s i| ≤ w s) :
    let L := ∫ s in a..z, w s
    (∀ t ∈ Icc a z, ∀ i, |originalUpperIntegralOne b a t i| ≤ L) ∧
    (∀ t ∈ Icc a z, ∀ i j, |originalUpperIntegralTwo b a t i j| ≤ L^2) ∧
    (∀ t ∈ Icc a z, ∀ i j l, |originalUpperIntegralThree b a t i j l| ≤ L^3) := by
  dsimp only
  let L := ∫ s in a..z, w s
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg haz hw0
  have h1 : ∀ t ∈ Icc a z, ∀ i, |originalUpperIntegralOne b a t i| ≤ L := by
    intro t ht i
    simpa [originalUpperIntegralOne, L] using
      originalUpper_weighted_integral_bound w (fun s => b s i) a z t 1 ht (by norm_num) hw hw0
        (fun s hs => by simpa using hb s ⟨hs.1, hs.2.trans ht.2⟩ i)
  have h2 : ∀ t ∈ Icc a z, ∀ i j, |originalUpperIntegralTwo b a t i j| ≤ L^2 := by
    intro t ht i j
    have h := originalUpper_weighted_integral_bound w
      (fun s => originalUpperIntegralOne b a s i * b s j) a z t L ht hL hw hw0 (by
        intro s hs
        have hs' : s ∈ Icc a z := ⟨hs.1, hs.2.trans ht.2⟩
        rw [abs_mul]
        exact mul_le_mul (h1 s hs' i) (hb s hs' j) (abs_nonneg _) hL)
    simpa [originalUpperIntegralTwo, L, pow_two] using h
  have h3 : ∀ t ∈ Icc a z, ∀ i j l, |originalUpperIntegralThree b a t i j l| ≤ L^3 := by
    intro t ht i j l
    have h := originalUpper_weighted_integral_bound w
      (fun s => originalUpperIntegralTwo b a s i j * b s l) a z t (L^2) ht (sq_nonneg _) hw hw0 (by
        intro s hs
        have hs' : s ∈ Icc a z := ⟨hs.1, hs.2.trans ht.2⟩
        rw [abs_mul]
        exact mul_le_mul (h2 s hs' i j) (hb s hs' l) (abs_nonneg _) (sq_nonneg _))
    simpa [originalUpperIntegralThree, L, pow_succ] using h
  exact ⟨h1,h2,h3⟩

theorem originalUpperOrderedSignature_norm_bound
    (b : ℝ → Fin 6 → ℝ) (w : ℝ → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hw : IntervalIntegrable w volume a z) (hw0 : ∀ s ∈ Icc a z, 0 ≤ w s)
    (hb : ∀ s ∈ Icc a z, ∀ i : Fin 6, |b s i| ≤ w s) :
    ‖originalUpperOrderedSignature b a z‖ ≤
      (∫ s in a..z, w s) * (1 + ∫ s in a..z, w s)^2 := by
  let L := ∫ s in a..z, w s
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg haz hw0
  obtain ⟨h1,h2,h3⟩ := originalUpper_ordered_integral_bounds b w a z haz hw hw0 hb
  have hz : z ∈ Icc a z := ⟨haz,le_rfl⟩
  have hpow : 0 ≤ L^3 := pow_nonneg hL _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (sq_nonneg _))).mpr
  intro i
  fin_cases i
  · change |originalUpperIntegralOne b a z 0| ≤ L*(1+L)^2
    have := h1 z hz 0
    nlinarith [sq_nonneg L]
  · change |originalUpperIntegralOne b a z 1 + originalUpperIntegralTwo b a z 0 3| ≤ L*(1+L)^2
    have := (abs_add _ _).trans (add_le_add (h1 z hz 1) (h2 z hz 0 3))
    nlinarith [sq_nonneg L]
  · change |originalUpperIntegralOne b a z 2 + originalUpperIntegralTwo b a z 0 4 +
      originalUpperIntegralTwo b a z 1 5 + originalUpperIntegralThree b a z 0 3 5| ≤ L*(1+L)^2
    calc
      _ ≤ |originalUpperIntegralOne b a z 2| + |originalUpperIntegralTwo b a z 0 4| +
          |originalUpperIntegralTwo b a z 1 5| + |originalUpperIntegralThree b a z 0 3 5| := by
            exact (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
              (add_le_add_right (abs_add _ _) _)) _)
      _ ≤ L + L^2 + L^2 + L^3 := add_le_add
        (add_le_add (add_le_add (h1 z hz 2) (h2 z hz 0 4)) (h2 z hz 1 5)) (h3 z hz 0 3 5)
      _ = L*(1+L)^2 := by ring
  · change |originalUpperIntegralOne b a z 3| ≤ L*(1+L)^2
    have := h1 z hz 3
    nlinarith [sq_nonneg L]
  · change |originalUpperIntegralOne b a z 4 + originalUpperIntegralTwo b a z 3 5| ≤ L*(1+L)^2
    have := (abs_add _ _).trans (add_le_add (h1 z hz 4) (h2 z hz 3 5))
    nlinarith [sq_nonneg L]
  · change |originalUpperIntegralOne b a z 5| ≤ L*(1+L)^2
    have := h1 z hz 5
    nlinarith [sq_nonneg L]

theorem originalUpperAffineInv_norm_bound (g : Fin 6 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ‖g‖ ≤ C) : ‖originalUpperAffineInv g‖ ≤ C*(1+C)^2 := by
  have hi (i : Fin 6) : |g i| ≤ C := (norm_le_pi_norm g i).trans hg
  have hij (i j : Fin 6) : |g i * g j| ≤ C^2 := by
    simpa [abs_mul, pow_two] using mul_le_mul (hi i) (hi j) (abs_nonneg _) hC
  have hijk (i j k : Fin 6) : |g i * g j * g k| ≤ C^3 := by
    rw [abs_mul]
    simpa [pow_succ] using mul_le_mul (hij i j) (hi k) (abs_nonneg _) (sq_nonneg C)
  have hC3 : 0 ≤ C^3 := pow_nonneg hC _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (sq_nonneg _))).mpr
  intro i
  fin_cases i
  · change |-g 0| ≤ _
    rw [abs_neg]; nlinarith [hi 0, sq_nonneg C]
  · change |g 0*g 3-g 1| ≤ _
    have := (abs_sub _ _).trans (add_le_add (hij 0 3) (hi 1))
    nlinarith [sq_nonneg C]
  · change |-g 2+g 0*g 4+g 1*g 5-g 0*g 3*g 5| ≤ _
    calc
      _ ≤ |-g 2|+|g 0*g 4|+|g 1*g 5|+|g 0*g 3*g 5| :=
        (abs_sub _ _).trans (add_le_add_right ((abs_add _ _).trans
          (add_le_add_right (abs_add _ _) _)) _)
      _ ≤ C+C^2+C^2+C^3 := by
        rw [abs_neg]
        exact add_le_add (add_le_add (add_le_add (hi 2) (hij 0 4)) (hij 1 5)) (hijk 0 3 5)
      _ = C*(1+C)^2 := by ring
  · change |-g 3| ≤ _
    rw [abs_neg]; nlinarith [hi 3, sq_nonneg C]
  · change |g 3*g 5-g 4| ≤ _
    have := (abs_sub _ _).trans (add_le_add (hij 3 5) (hi 4))
    nlinarith [sq_nonneg C]
  · change |-g 5| ≤ _
    rw [abs_neg]; nlinarith [hi 5, sq_nonneg C]

theorem originalUpperRelativeFrame_reverse (g h : Fin 6 → ℝ) :
    originalUpperRelativeFrame h g = originalUpperAffineInv (originalUpperRelativeFrame g h) := by
  ext i
  fin_cases i <;> simp [originalUpperRelativeFrame, originalUpperAffineComp, originalUpperAffineInv] <;> ring

theorem originalUpperRelativeFrame_norm_bounds
    (g b : ℝ → Fin 6 → ℝ) (w : ℝ → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z))
    (hg : ∀ t ∈ Icc a z, HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hw : IntervalIntegrable w volume a z) (hw0 : ∀ s ∈ Icc a z, 0 ≤ w s)
    (hbw : ∀ s ∈ Icc a z, ∀ i : Fin 6, |b s i| ≤ w s) :
    let L := ∫ s in a..z, w s
    let C := L*(1+L)^2
    ‖originalUpperRelativeFrame (g a) (g z)‖ ≤ C ∧
      ‖originalUpperRelativeFrame (g z) (g a)‖ ≤ C*(1+C)^2 := by
  dsimp only
  have h := originalUpperOrderedSignature_norm_bound b w a z haz hw hw0 hbw
  rw [← originalUpperRelativeFrame_ordered_integrals g b a z haz hb hg] at h
  refine ⟨h,?_⟩
  rw [originalUpperRelativeFrame_reverse]
  exact originalUpperAffineInv_norm_bound _ _
    (mul_nonneg (intervalIntegral.integral_nonneg haz hw0) (sq_nonneg _)) h

end PaperI
