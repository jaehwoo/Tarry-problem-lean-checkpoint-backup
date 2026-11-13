import PaperILean.DominantCoordinateGraphs

/-! The two derivative signs for x+y and x-y select one fixed signed
coordinate cone on a whole interval. Stationary values and constant pieces
are allowed. The resulting closed image is a Lipschitz graph. -/

noncomputable section
namespace PaperI
open Set

theorem derivativeSignOn_weak {f : ℝ → ℝ} {S : Set ℝ}
    (h : DerivativeSignOn f S) :
    (∀ t ∈ S, 0 ≤ deriv f t) ∨ (∀ t ∈ S, deriv f t ≤ 0) := by
  rcases h with hp | hn | hz
  · exact Or.inl (fun t ht => (hp t ht).le)
  · exact Or.inr (fun t ht => (hn t ht).le)
  · exact Or.inl (fun t ht => (hz t ht).ge)

theorem coordinate_cone_of_sum_sub_signs (u v : ℝ → ℝ) (S : Set ℝ)
    (hp : (∀ t ∈ S, 0 ≤ u t+v t) ∨ (∀ t ∈ S, u t+v t ≤ 0))
    (hm : (∀ t ∈ S, 0 ≤ u t-v t) ∨ (∀ t ∈ S, u t-v t ≤ 0)) :
    (∀ t ∈ S, |v t| ≤ u t) ∨ (∀ t ∈ S, |v t| ≤ -u t) ∨
      (∀ t ∈ S, |u t| ≤ v t) ∨ (∀ t ∈ S, |u t| ≤ -v t) := by
  rcases hp with hp | hp <;> rcases hm with hm | hm
  · exact Or.inl (fun t ht => abs_le.mpr ⟨by linarith [hp t ht],by linarith [hm t ht]⟩)
  · exact Or.inr (Or.inr (Or.inl (fun t ht => abs_le.mpr ⟨by linarith [hp t ht],by linarith [hm t ht]⟩)))
  · exact Or.inr (Or.inr (Or.inr (fun t ht => abs_le.mpr ⟨by linarith [hm t ht],by linarith [hp t ht]⟩)))
  · exact Or.inr (Or.inl (fun t ht => abs_le.mpr ⟨by linarith [hm t ht],by linarith [hp t ht]⟩))

theorem derivative_coordinate_cone_of_signs {f g : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b)) (hg : DifferentiableOn ℝ g (Ioo a b))
    (hp : DerivativeSignOn (fun t => f t+g t) (Ioo a b))
    (hm : DerivativeSignOn (fun t => f t-g t) (Ioo a b)) :
    (∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t) ∨
      (∀ t ∈ Ioo a b, |deriv g t| ≤ -deriv f t) ∨
      (∀ t ∈ Ioo a b, |deriv f t| ≤ deriv g t) ∨
      (∀ t ∈ Ioo a b, |deriv f t| ≤ -deriv g t) := by
  have hadd t (ht : t ∈ Ioo a b) := deriv_add
    ((hf t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
    ((hg t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  have hsub t (ht : t ∈ Ioo a b) := deriv_sub
    ((hf t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
    ((hg t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
  apply coordinate_cone_of_sum_sub_signs (deriv f) (deriv g) (Ioo a b)
  · rcases derivativeSignOn_weak hp with h | h
    · exact Or.inl (fun t ht => by simpa only [hadd t ht] using h t ht)
    · exact Or.inr (fun t ht => by simpa only [hadd t ht] using h t ht)
  · rcases derivativeSignOn_weak hm with h | h
    · exact Or.inl (fun t ht => by simpa only [hsub t ht] using h t ht)
    · exact Or.inr (fun t ht => by simpa only [hsub t ht] using h t ht)

/-- Exact closed-interval graph data in one of the four signed coordinate
directions. Point images are retained; no nonzero tangent is asserted there. -/
def SignedPlanarGraphArc (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) : Prop :=
  ∃ i j : Fin 2, i ≠ j ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
    MonotoneOn (fun t => σ * γ t i) (Icc a b) ∧
    (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ∀ k, |γ u k-γ v k| ≤ |γ u i-γ v i|) ∧
    ∃ h : ℝ → ℝ, LipschitzOnWith 1 h (Icc (σ*γ a i) (σ*γ b i)) ∧
      (∀ t ∈ Icc a b, h (σ*γ t i)=γ t j) ∧
      ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q

theorem signedPlanarGraphArc_of_cone {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ∀ k, ContinuousOn (fun t => γ t k) (Icc a b))
    (hd : ∀ k, DifferentiableOn ℝ (fun t => γ t k) (Ioo a b))
    (i j : Fin 2) (hij : i ≠ j) (σ : ℝ) (hσ : σ=1 ∨ σ= -1)
    (hdom : ∀ t ∈ Ioo a b, |deriv (fun r => γ r j) t| ≤ σ * deriv (fun r => γ r i) t) :
    SignedPlanarGraphArc γ a b := by
  let f := fun t => σ*γ t i
  let g := fun t => γ t j
  have hcf : ContinuousOn f (Icc a b) := continuousOn_const.mul (hc i)
  have hdf : DifferentiableOn ℝ f (Ioo a b) := (differentiableOn_const σ).mul (hd i)
  have hdom' : ∀ t ∈ Ioo a b, |deriv g t| ≤ deriv f t := by
    intro t ht
    simpa only [f,g,deriv_const_mul_field] using hdom t ht
  obtain ⟨hm,h,hEq,hLip⟩ := exists_lipschitz_graph_of_dominant_derivative hcf (hc j) hdf (hd j) hdom'
  have hImage := monotone_continuous_image_interval hab hcf hm
  have hbound := dominant_derivative_abs_secant hcf (hc j) hdf (hd j) hdom'
  have hs (u v : ℝ) : |f u-f v|=|γ u i-γ v i| := by
    rcases hσ with rfl | rfl
    · simp [f]
    · simp only [f,neg_one_mul,neg_sub_neg,abs_sub_comm]
  refine ⟨i,j,hij,σ,hσ,hm,?_,h,?_,hEq,?_⟩
  · intro u hu v hv k
    have hk : k=i ∨ k=j := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    rcases hk with rfl | rfl
    · exact le_rfl
    · simpa only [g,hs u v] using hbound u hu v hv
  · simpa only [hImage] using hLip
  · intro q hq
    have := hImage.symm ▸ hq
    exact this

theorem signedPlanarGraphArc_of_sum_sub_signs {γ : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ∀ k, ContinuousOn (fun t => γ t k) (Icc a b))
    (hd : ∀ k, DifferentiableOn ℝ (fun t => γ t k) (Ioo a b))
    (hp : DerivativeSignOn (fun t => γ t 0+γ t 1) (Ioo a b))
    (hm : DerivativeSignOn (fun t => γ t 0-γ t 1) (Ioo a b)) : SignedPlanarGraphArc γ a b := by
  rcases derivative_coordinate_cone_of_signs (hd 0) (hd 1) hp hm with h | h | h | h
  · exact signedPlanarGraphArc_of_cone hab hc hd 0 1 (by decide) 1 (Or.inl rfl)
      (by simpa only [one_mul] using h)
  · exact signedPlanarGraphArc_of_cone hab hc hd 0 1 (by decide) (-1) (Or.inr rfl)
      (by simpa only [neg_one_mul] using h)
  · exact signedPlanarGraphArc_of_cone hab hc hd 1 0 (by decide) 1 (Or.inl rfl)
      (by simpa only [one_mul] using h)
  · exact signedPlanarGraphArc_of_cone hab hc hd 1 0 (by decide) (-1) (Or.inr rfl)
      (by simpa only [neg_one_mul] using h)

end PaperI
