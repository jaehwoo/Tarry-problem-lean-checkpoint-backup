import PaperILean.OriginalUpperIntegralBounds
import PaperILean.DerivativeSignSubdivision

/-! The original derivative-sign/variation estimate gives the compact body
integral bound required before passing singular path endpoints. -/
noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped BigOperators

/-- Every compact portion of an analytic derivative-sign piece contributes
at most twice the coefficient bound. Signs refer to the actual derivative. -/
theorem originalHaar_coefficient_derivative_integral
    (f f' : ℝ → ℝ) (a z u v B : ℝ) (hB : 0 ≤ B)
    (hu : u ∈ Ioo a z) (hv : v ∈ Ioo a z) (huv : u ≤ v)
    (hderiv : ∀ t ∈ Ioo a z, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Ioo a z))
    (hsign : DerivativeSignOn f (Ioo a z))
    (hrange : ∀ t ∈ Ioo a z, |f t| ≤ B) :
    (∫ t in u..v, |f' t|) ≤ 2*B := by
  have hsub : Icc u v ⊆ Ioo a z := fun t ht =>
    ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
  have hf' : ContinuousOn f' (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact hcont.mono hsub
  have hint : IntervalIntegrable f' volume u v := hf'.intervalIntegrable
  have hftc : (∫ t in u..v, f' t) = f v-f u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (hsub (by simpa [uIcc_of_le huv] using ht))) hint
  have hfu := (abs_le.mp (hrange u hu))
  have hfv := (abs_le.mp (hrange v hv))
  rcases hsign with hp | hn | hz
  · have heq : (∫ t in u..v, |f' t|) = ∫ t in u..v, f' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' := hsub (by simpa [uIcc_of_le huv] using ht)
      exact abs_of_nonneg (by rw [← (hderiv t ht').deriv]; exact (hp t ht').le)
    rw [heq,hftc]
    linarith
  · have heq : (∫ t in u..v, |f' t|) = ∫ t in u..v, -f' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' := hsub (by simpa [uIcc_of_le huv] using ht)
      exact abs_of_nonpos (by rw [← (hderiv t ht').deriv]; exact (hn t ht').le)
    rw [heq,intervalIntegral.integral_neg,hftc]
    linarith
  · have heq : (∫ t in u..v, |f' t|) = 0 := by
      calc
        _ = ∫ t in u..v, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' := hsub (by simpa [uIcc_of_le huv] using ht)
          have he : f' t=0 := by rw [← (hderiv t ht').deriv]; exact hz t ht'
          simp [he]
        _ = 0 := by simp
    rw [heq]
    positivity

/-- Summing the actual coordinate derivative estimates gives a continuous
body majorant on every compact interior interval. The remaining pivot
application is the pointwise inequality feeding this particular majorant. -/
theorem originalHaar_coefficient_body_majorant_integral
    {ι : Type*} [Fintype ι]
    (q q' : ι → ℝ → ℝ) (a z u v B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hu : u ∈ Ioo a z) (hv : v ∈ Ioo a z) (huv : u ≤ v)
    (hderiv : ∀ i t, t ∈ Ioo a z → HasDerivAt (q i) (q' i t) t)
    (hcont : ∀ i, ContinuousOn (q' i) (Ioo a z))
    (hsign : ∀ i, DerivativeSignOn (q i) (Ioo a z))
    (hrange : ∀ i t, t ∈ Ioo a z → |q i t| ≤ B) :
    (∫ t in u..v, H*∑ i, |q' i t|) ≤ H*(Fintype.card ι:ℝ)*(2*B) := by
  have hsub : Icc u v ⊆ Ioo a z := fun t ht =>
    ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
  have hint (i : ι) : IntervalIntegrable (fun t => |q' i t|) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact (hcont i).abs.mono hsub
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finset_sum]
  · calc
      H * ∑ i, (∫ t in u..v, |q' i t|) ≤ H*∑ _i : ι, 2*B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
          originalHaar_coefficient_derivative_integral (q i) (q' i) a z u v B
            hB hu hv huv (hderiv i) (hcont i) (hsign i) (hrange i))) hH
      _ = H*(Fintype.card ι:ℝ)*(2*B) := by simp [mul_assoc]
  · intro i _
    exact hint i

end PaperI
