import PaperILean.OriginalUpperIntegralBounds

/-! Ordered-integral perturbation for I1480[363,533). The one-, two- and
three-factor integrals retain their original time order. Continuity justifies
every subtraction of integrals. Sign conditions on M and eps follow from
the stated bounds at the endpoint a, even when the interval has length zero. -/

noncomputable section
namespace PaperI.OrderedIntegralPerturbation
open Set MeasureTheory

private theorem integral_abs_le_const_length
    (f : ℝ → ℝ) (a z t K : ℝ) (ht : t ∈ Icc a z) (hK : 0 ≤ K)
    (hf : ∀ s ∈ Icc a t, |f s| ≤ K) :
    |∫ s in a..t, f s| ≤ K * (z - a) := by
  have h := originalUpper_weighted_integral_bound (fun _ => (1 : ℝ)) f a z t K ht hK
    (continuous_const.intervalIntegrable a z) (fun _ _ => zero_le_one)
    (fun s hs => by simpa only [mul_one] using hf s hs)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h

private theorem product_difference_bound (u v U V : ℝ) :
    |u * v - U * V| ≤ |u - U| * |v| + |U| * |v - V| := by
  calc
    |u * v - U * V| = |(u - U) * v + U * (v - V)| := by congr 1; ring
    _ ≤ |(u - U) * v| + |U * (v - V)| := abs_add _ _
    _ = _ := by rw [abs_mul, abs_mul]

/-- Uniform errors for all original ordered levels on the actual interval. -/
theorem ordered_integral_error_bounds
    (b c : ℝ → Fin 6 → ℝ) (a z M eps : ℝ) (haz : a ≤ z)
    (hb : ContinuousOn b (Icc a z)) (hc : ContinuousOn c (Icc a z))
    (hbM : ∀ t ∈ Icc a z, ∀ i : Fin 6, |b t i| ≤ M)
    (hcM : ∀ t ∈ Icc a z, ∀ i : Fin 6, |c t i| ≤ M)
    (herr : ∀ t ∈ Icc a z, ∀ i : Fin 6, |b t i - c t i| ≤ eps) :
    (∀ t ∈ Icc a z, ∀ i : Fin 6,
      |originalUpperIntegralOne b a t i - originalUpperIntegralOne c a t i| ≤
        eps * (z - a)) ∧
    (∀ t ∈ Icc a z, ∀ i j : Fin 6,
      |originalUpperIntegralTwo b a t i j - originalUpperIntegralTwo c a t i j| ≤
        2 * M * eps * (z - a) ^ 2) ∧
    (∀ t ∈ Icc a z, ∀ i j l : Fin 6,
      |originalUpperIntegralThree b a t i j l - originalUpperIntegralThree c a t i j l| ≤
        3 * M ^ 2 * eps * (z - a) ^ 3) := by
  have ha : a ∈ Icc a z := ⟨le_rfl, haz⟩
  have hM : 0 ≤ M := (abs_nonneg (b a 0)).trans (hbM a ha 0)
  have heps : 0 ≤ eps := (abs_nonneg (b a 0 - c a 0)).trans (herr a ha 0)
  have hL : 0 ≤ z - a := sub_nonneg.mpr haz
  have hb' : ContinuousOn b (uIcc a z) := by simpa only [uIcc_of_le haz] using hb
  have hc' : ContinuousOn c (uIcc a z) := by simpa only [uIcc_of_le haz] using hc
  have hbi (i : Fin 6) : ContinuousOn (fun t => b t i) (uIcc a z) :=
    (continuous_apply i).comp_continuousOn hb'
  have hci (i : Fin 6) : ContinuousOn (fun t => c t i) (uIcc a z) :=
    (continuous_apply i).comp_continuousOn hc'
  have hsub {t : ℝ} (ht : t ∈ Icc a z) : uIcc a t ⊆ uIcc a z := by
    rw [uIcc_of_le ht.1, uIcc_of_le haz]
    exact fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hsub' {t : ℝ} (ht : t ∈ Icc a z) : Icc a t ⊆ Icc a z :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have habs := originalUpper_ordered_integral_bounds c (fun _ => M) a z haz
    (continuous_const.intervalIntegrable a z) (fun _ _ => hM) hcM
  dsimp only at habs
  have hconst : (∫ s in a..z, M) = M * (z - a) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hconst] at habs
  have h1 : ∀ t ∈ Icc a z, ∀ i : Fin 6,
      |originalUpperIntegralOne b a t i - originalUpperIntegralOne c a t i| ≤
        eps * (z - a) := by
    intro t ht i
    have he : originalUpperIntegralOne b a t i - originalUpperIntegralOne c a t i =
        ∫ s in a..t, b s i - c s i := by
      exact (intervalIntegral.integral_sub
        ((hbi i).mono (hsub ht)).intervalIntegrable
        ((hci i).mono (hsub ht)).intervalIntegrable).symm
    rw [he]
    exact integral_abs_le_const_length _ a z t eps ht heps
      (fun s hs => herr s (hsub' ht hs) i)
  have h2 : ∀ t ∈ Icc a z, ∀ i j : Fin 6,
      |originalUpperIntegralTwo b a t i j - originalUpperIntegralTwo c a t i j| ≤
        2 * M * eps * (z - a) ^ 2 := by
    intro t ht i j
    have he : originalUpperIntegralTwo b a t i j - originalUpperIntegralTwo c a t i j =
        ∫ s in a..t, originalUpperIntegralOne b a s i * b s j -
          originalUpperIntegralOne c a s i * c s j := by
      exact (intervalIntegral.integral_sub
        (((originalUpperIntegralOne_continuousOn b a z hb' i).mul (hbi j)).mono
          (hsub ht)).intervalIntegrable
        (((originalUpperIntegralOne_continuousOn c a z hc' i).mul (hci j)).mono
          (hsub ht)).intervalIntegrable).symm
    have hbound : ∀ s ∈ Icc a t,
        |originalUpperIntegralOne b a s i * b s j -
          originalUpperIntegralOne c a s i * c s j| ≤ 2 * M * eps * (z - a) := by
      intro s hs
      have hs' := hsub' ht hs
      calc
        _ ≤ |originalUpperIntegralOne b a s i - originalUpperIntegralOne c a s i| *
              |b s j| + |originalUpperIntegralOne c a s i| * |b s j - c s j| :=
          product_difference_bound _ _ _ _
        _ ≤ (eps * (z - a)) * M + (M * (z - a)) * eps :=
          add_le_add
            (mul_le_mul (h1 s hs' i) (hbM s hs' j) (abs_nonneg _) (mul_nonneg heps hL))
            (mul_le_mul (habs.1 s hs' i) (herr s hs' j) (abs_nonneg _) (mul_nonneg hM hL))
        _ = _ := by ring
    rw [he]
    have h := integral_abs_le_const_length _ a z t (2 * M * eps * (z - a)) ht
      (by positivity) hbound
    convert h using 1
    ring
  have h3 : ∀ t ∈ Icc a z, ∀ i j l : Fin 6,
      |originalUpperIntegralThree b a t i j l - originalUpperIntegralThree c a t i j l| ≤
        3 * M ^ 2 * eps * (z - a) ^ 3 := by
    intro t ht i j l
    have he : originalUpperIntegralThree b a t i j l - originalUpperIntegralThree c a t i j l =
        ∫ s in a..t, originalUpperIntegralTwo b a s i j * b s l -
          originalUpperIntegralTwo c a s i j * c s l := by
      exact (intervalIntegral.integral_sub
        (((originalUpperIntegralTwo_continuousOn b a z hb' i j).mul (hbi l)).mono
          (hsub ht)).intervalIntegrable
        (((originalUpperIntegralTwo_continuousOn c a z hc' i j).mul (hci l)).mono
          (hsub ht)).intervalIntegrable).symm
    have hbound : ∀ s ∈ Icc a t,
        |originalUpperIntegralTwo b a s i j * b s l -
          originalUpperIntegralTwo c a s i j * c s l| ≤
            3 * M ^ 2 * eps * (z - a) ^ 2 := by
      intro s hs
      have hs' := hsub' ht hs
      calc
        _ ≤ |originalUpperIntegralTwo b a s i j - originalUpperIntegralTwo c a s i j| *
              |b s l| + |originalUpperIntegralTwo c a s i j| * |b s l - c s l| :=
          product_difference_bound _ _ _ _
        _ ≤ (2 * M * eps * (z - a) ^ 2) * M + (M * (z - a)) ^ 2 * eps :=
          add_le_add
            (mul_le_mul (h2 s hs' i j) (hbM s hs' l) (abs_nonneg _) (by positivity))
            (mul_le_mul (habs.2.1 s hs' i j) (herr s hs' l) (abs_nonneg _) (sq_nonneg _))
        _ = _ := by ring
    rw [he]
    have h := integral_abs_le_const_length _ a z t (3 * M ^ 2 * eps * (z - a) ^ 2) ht
      (by positivity) hbound
    convert h using 1
    ring
  exact ⟨h1, h2, h3⟩

end PaperI.OrderedIntegralPerturbation
