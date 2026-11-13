import PaperILean.DerivativeSignSubdivision
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue

/-! I1263 local graph conversion without a nonvanishing-speed assumption.
Weak signed derivative domination gives secant domination on the closed
interval. Equal longitudinal values force equal transverse values, including
stationary time intervals. No inverse-time regularity is assumed. -/

noncomputable section
namespace PaperI
open Set

theorem dominant_derivative_secant
    {f g : ℝ → ℝ} {a b : ℝ}
    (hcF : ContinuousOn f (Icc a b)) (hcG : ContinuousOn g (Icc a b))
    (hdF : DifferentiableOn ℝ f (Ioo a b)) (hdG : DifferentiableOn ℝ g (Ioo a b))
    (hdom : ∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → |g v - g u| ≤ f v - f u := by
  have hm : MonotoneOn (fun t => f t - g t) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcF.sub hcG)
      (by simpa only [interior_Icc] using hdF.sub hdG)
    intro t ht
    rw [interior_Icc] at ht
    rw [deriv_sub ((hdF t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
      ((hdG t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))]
    have h := (abs_le.mp (hdom t ht)).2
    linarith
  have hp : MonotoneOn (fun t => f t + g t) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcF.add hcG)
      (by simpa only [interior_Icc] using hdF.add hdG)
    intro t ht
    rw [interior_Icc] at ht
    rw [deriv_add ((hdF t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
      ((hdG t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))]
    have h := (abs_le.mp (hdom t ht)).1
    linarith
  intro u hu v hv huv
  have h1 := hm hu hv huv
  have h2 := hp hu hv huv
  dsimp only at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem dominant_derivative_monotone
    {f g : ℝ → ℝ} {a b : ℝ}
    (hcF : ContinuousOn f (Icc a b)) (hcG : ContinuousOn g (Icc a b))
    (hdF : DifferentiableOn ℝ f (Ioo a b)) (hdG : DifferentiableOn ℝ g (Ioo a b))
    (hdom : ∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t) : MonotoneOn f (Icc a b) := by
  intro u hu v hv huv
  have h := (abs_nonneg (g v-g u)).trans
    (dominant_derivative_secant hcF hcG hdF hdG hdom u hu v hv huv)
  linarith

theorem dominant_derivative_abs_secant
    {f g : ℝ → ℝ} {a b : ℝ}
    (hcF : ContinuousOn f (Icc a b)) (hcG : ContinuousOn g (Icc a b))
    (hdF : DifferentiableOn ℝ f (Ioo a b)) (hdG : DifferentiableOn ℝ g (Ioo a b))
    (hdom : ∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |g u-g v| ≤ |f u-f v| := by
  have h := dominant_derivative_secant hcF hcG hdF hdG hdom
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (g u),abs_sub_comm (f u)]
    exact (h u hu v hv huv).trans (le_abs_self _)
  · exact (h v hv u hu hvu).trans (le_abs_self _)

/-- A set-theoretic graph factorization with the exact Lipschitz constant1.
The values outside the actual longitudinal image are immaterial. -/
theorem exists_lipschitz_graph_of_secant_domination
    (S : Set ℝ) (f g : ℝ → ℝ)
    (hbound : ∀ u ∈ S, ∀ v ∈ S, |g u-g v| ≤ |f u-f v|) :
    ∃ h : ℝ → ℝ, (∀ t ∈ S, h (f t) = g t) ∧ LipschitzOnWith 1 h (f '' S) := by
  classical
  let h := fun q => if hq : q ∈ f '' S then g (Classical.choose hq) else 0
  have he (t : ℝ) (ht : t ∈ S) : h (f t) = g t := by
    have hq : f t ∈ f '' S := mem_image_of_mem f ht
    have hp := Classical.choose_spec hq
    have hz : |g (Classical.choose hq)-g t| ≤ 0 := by
      simpa only [hp.2,sub_self,abs_zero] using hbound _ hp.1 t ht
    have heq : g (Classical.choose hq)=g t := sub_eq_zero.mp
      (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
    simpa only [h,dif_pos hq] using heq
  refine ⟨h,he,?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
  simpa only [he u hu,he v hv,Real.dist_eq,NNReal.coe_one,one_mul] using hbound u hu v hv

theorem exists_lipschitz_graph_of_dominant_derivative
    {f g : ℝ → ℝ} {a b : ℝ}
    (hcF : ContinuousOn f (Icc a b)) (hcG : ContinuousOn g (Icc a b))
    (hdF : DifferentiableOn ℝ f (Ioo a b)) (hdG : DifferentiableOn ℝ g (Ioo a b))
    (hdom : ∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t) :
    MonotoneOn f (Icc a b) ∧
      ∃ h : ℝ → ℝ, (∀ t ∈ Icc a b, h (f t)=g t) ∧ LipschitzOnWith 1 h (f '' Icc a b) := by
  exact ⟨dominant_derivative_monotone hcF hcG hdF hdG hdom,
    exists_lipschitz_graph_of_secant_domination _ f g
      (dominant_derivative_abs_secant hcF hcG hdF hdG hdom)⟩

theorem monotone_continuous_image_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (hm : MonotoneOn f (Icc a b)) :
    f '' Icc a b = Icc (f a) (f b) :=
  Subset.antisymm hm.image_Icc_subset (intermediate_value_Icc hab hc)

end PaperI
