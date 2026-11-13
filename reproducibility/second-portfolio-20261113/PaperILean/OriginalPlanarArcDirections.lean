import PaperILean.PlanarTangentProjection

/-! I1263: retain the SAME coordinate direction in the derivative cone,
closed Lipschitz graph, and normalized tangent estimate. Stationary points
and constant images are retained; normalization requires positive speed. -/

noncomputable section
namespace PaperI
open Set

def DirectedPlanarGraphArc (g : ℝ → Fin 2 → ℝ) (a b : ℝ)
    (i k : Fin 2) (σ : ℝ) : Prop :=
  i ≠ k ∧ (σ = 1 ∨ σ = -1) ∧
    MonotoneOn (fun t => σ * g t i) (Icc a b) ∧
    (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ∀ c,
      |g u c - g v c| ≤ |g u i - g v i|) ∧
    ∃ h : ℝ → ℝ, LipschitzOnWith 1 h (Icc (σ*g a i) (σ*g b i)) ∧
      (∀ t ∈ Icc a b, h (σ*g t i) = g t k) ∧
      ∀ q ∈ Icc (σ*g a i) (σ*g b i), ∃ t ∈ Icc a b, σ*g t i = q

theorem DirectedPlanarGraphArc.to_signed {g : ℝ → Fin 2 → ℝ} {a b σ : ℝ}
    {i k : Fin 2} (h : DirectedPlanarGraphArc g a b i k σ) :
    SignedPlanarGraphArc g a b :=
  ⟨i,k,h.1,σ,h.2⟩

theorem directedPlanarGraphArc_of_cone {g : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ∀ k, ContinuousOn (fun t => g t k) (Icc a b))
    (hd : ∀ k, DifferentiableOn ℝ (fun t => g t k) (Ioo a b))
    (i k : Fin 2) (hik : i ≠ k) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hdom : ∀ t ∈ Ioo a b,
      |deriv (fun r => g r k) t| ≤ σ * deriv (fun r => g r i) t) :
    DirectedPlanarGraphArc g a b i k σ := by
  let f := fun t => σ*g t i
  let h := fun t => g t k
  have hcf : ContinuousOn f (Icc a b) := continuousOn_const.mul (hc i)
  have hdf : DifferentiableOn ℝ f (Ioo a b) := (differentiableOn_const σ).mul (hd i)
  have hdom' : ∀ t ∈ Ioo a b, |deriv h t| ≤ deriv f t := by
    intro t ht
    simpa only [f,h,deriv_const_mul_field] using hdom t ht
  obtain ⟨hm,F,hEq,hLip⟩ :=
    exists_lipschitz_graph_of_dominant_derivative hcf (hc k) hdf (hd k) hdom'
  have hImage := monotone_continuous_image_interval hab hcf hm
  have hbound := dominant_derivative_abs_secant hcf (hc k) hdf (hd k) hdom'
  have hs (u v : ℝ) : |f u-f v| = |g u i-g v i| := by
    rcases hσ with rfl | rfl
    · simp [f]
    · simp only [f,neg_one_mul,neg_sub_neg,abs_sub_comm]
  refine ⟨hik,hσ,hm,?_,F,?_,hEq,?_⟩
  · intro u hu v hv c
    have hck : c=i ∨ c=k := by fin_cases i <;> fin_cases k <;> fin_cases c <;> simp_all
    rcases hck with rfl | rfl
    · exact le_rfl
    · simpa only [h,hs u v] using hbound u hu v hv
  · simpa only [hImage] using hLip
  · intro q hq
    have hh := hImage.symm ▸ hq
    exact hh

def OriginalPlanarGraphArc (g : ℝ → Fin 2 → ℝ) (a b : ℝ) : Prop :=
  ∃ (i k : Fin 2) (σ : ℝ), DirectedPlanarGraphArc g a b i k σ ∧
    ∀ t ∈ Ioo a b, |deriv (fun r => g r k) t| ≤ σ * deriv (fun r => g r i) t

theorem originalPlanarGraphArc_of_sum_sub_signs {g : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ∀ k, ContinuousOn (fun t => g t k) (Icc a b))
    (hd : ∀ k, DifferentiableOn ℝ (fun t => g t k) (Ioo a b))
    (hp : DerivativeSignOn (fun t => g t 0+g t 1) (Ioo a b))
    (hm : DerivativeSignOn (fun t => g t 0-g t 1) (Ioo a b)) :
    OriginalPlanarGraphArc g a b := by
  rcases derivative_coordinate_cone_of_signs (hd 0) (hd 1) hp hm with h | h | h | h
  · have h' : ∀ t ∈ Ioo a b, |deriv (fun r => g r 1) t| ≤
        (1:ℝ)*deriv (fun r => g r 0) t := by simpa only [one_mul] using h
    exact ⟨0,1,1,directedPlanarGraphArc_of_cone hab hc hd 0 1 (by decide) 1 (Or.inl rfl) h',h'⟩
  · have h' : ∀ t ∈ Ioo a b, |deriv (fun r => g r 1) t| ≤
        (-1:ℝ)*deriv (fun r => g r 0) t := by simpa only [neg_one_mul] using h
    exact ⟨0,1,-1,directedPlanarGraphArc_of_cone hab hc hd 0 1 (by decide) (-1) (Or.inr rfl) h',h'⟩
  · have h' : ∀ t ∈ Ioo a b, |deriv (fun r => g r 0) t| ≤
        (1:ℝ)*deriv (fun r => g r 1) t := by simpa only [one_mul] using h
    exact ⟨1,0,1,directedPlanarGraphArc_of_cone hab hc hd 1 0 (by decide) 1 (Or.inl rfl) h',h'⟩
  · have h' : ∀ t ∈ Ioo a b, |deriv (fun r => g r 0) t| ≤
        (-1:ℝ)*deriv (fun r => g r 1) t := by simpa only [neg_one_mul] using h
    exact ⟨1,0,-1,directedPlanarGraphArc_of_cone hab hc hd 1 0 (by decide) (-1) (Or.inr rfl) h',h'⟩

theorem OriginalPlanarGraphArc.to_signed {g : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (h : OriginalPlanarGraphArc g a b) : SignedPlanarGraphArc g a b := by
  obtain ⟨i,k,σ,hg,_⟩ := h
  exact hg.to_signed

theorem OriginalPlanarGraphArc.tangent_projection {g : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (h : OriginalPlanarGraphArc g a b) :
    ∃ (i k : Fin 2) (σ : ℝ), DirectedPlanarGraphArc g a b i k σ ∧
      ∀ t ∈ Ioo a b,
        0 < (deriv (fun r => g r i) t)^2 + (deriv (fun r => g r k) t)^2 →
        (1/2:ℝ) ≤ σ * deriv (fun r => g r i) t /
          Real.sqrt ((deriv (fun r => g r i) t)^2 + (deriv (fun r => g r k) t)^2) := by
  obtain ⟨i,k,σ,hg,hdom⟩ := h
  refine ⟨i,k,σ,hg,?_⟩
  intro t ht hspeed
  apply dominant_nonzero_normalized_projection_half
    (v := deriv (fun r => g r k) t) (Real.sqrt_pos.mpr hspeed)
  · rw [Real.sq_sqrt hspeed.le]
    rcases hg.2.1 with hσ | hσ <;> simp [hσ]
  · exact hdom t ht

end PaperI
