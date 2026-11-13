import PaperILean.ExponentialSumCalculus

/-! Second-derivative assembly with explicit differentiability hypotheses.
Empty finite sums and arbitrary real scalar coefficients are retained. -/
noncomputable section
open scoped BigOperators
namespace PaperI

theorem differentiable_deriv_add (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : Differentiable ℝ (deriv f))
    (hg' : Differentiable ℝ (deriv g)) :
    Differentiable ℝ (deriv (fun t => f t + g t)) := by
  have h : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t :=
    funext (fun t => deriv_add (hf t) (hg t))
  rw [h]
  exact hf'.add hg'

theorem differentiable_deriv_sub (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : Differentiable ℝ (deriv f))
    (hg' : Differentiable ℝ (deriv g)) :
    Differentiable ℝ (deriv (fun t => f t - g t)) := by
  have h : deriv (fun t => f t - g t) = fun t => deriv f t - deriv g t :=
    funext (fun t => deriv_sub (hf t) (hg t))
  rw [h]
  exact hf'.sub hg'

theorem differentiable_deriv_const_mul (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (a : ℝ) :
    Differentiable ℝ (deriv (fun t => a * f t)) := by
  have h : deriv (fun t => a * f t) = fun t => a * deriv f t :=
    funext (fun t => deriv_const_mul a (hf t))
  rw [h]
  exact hf'.const_mul a

theorem differentiable_deriv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i))
    (hf' : ∀ i ∈ s, Differentiable ℝ (deriv (f i))) :
    Differentiable ℝ (deriv (fun t => ∑ i ∈ s, f i t)) := by
  have h : deriv (fun t => ∑ i ∈ s, f i t) = fun t => ∑ i ∈ s, deriv (f i) t :=
    funext (fun t => deriv_sum (fun i hi => hf i hi t))
  rw [h]
  exact Differentiable.sum hf'

theorem deriv2_add (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : Differentiable ℝ (deriv f))
    (hg' : Differentiable ℝ (deriv g)) (t : ℝ) :
    deriv (deriv (fun t => f t + g t)) t = deriv (deriv f) t + deriv (deriv g) t := by
  have h : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t :=
    funext (fun t => deriv_add (hf t) (hg t))
  rw [h, deriv_add (hf' t) (hg' t)]

theorem deriv2_sub (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : Differentiable ℝ (deriv f))
    (hg' : Differentiable ℝ (deriv g)) (t : ℝ) :
    deriv (deriv (fun t => f t - g t)) t = deriv (deriv f) t - deriv (deriv g) t := by
  have h : deriv (fun t => f t - g t) = fun t => deriv f t - deriv g t :=
    funext (fun t => deriv_sub (hf t) (hg t))
  rw [h, deriv_sub (hf' t) (hg' t)]

theorem deriv2_const_mul (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (a t : ℝ) :
    deriv (deriv (fun t => a * f t)) t = a * deriv (deriv f) t := by
  have h : deriv (fun t => a * f t) = fun t => a * deriv f t :=
    funext (fun t => deriv_const_mul a (hf t))
  rw [h, deriv_const_mul a (hf' t)]

theorem deriv2_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i))
    (hf' : ∀ i ∈ s, Differentiable ℝ (deriv (f i))) (t : ℝ) :
    deriv (deriv (fun t => ∑ i ∈ s, f i t)) t = ∑ i ∈ s, deriv (deriv (f i)) t := by
  have h : deriv (fun t => ∑ i ∈ s, f i t) = fun t => ∑ i ∈ s, deriv (f i) t :=
    funext (fun t => deriv_sum (fun i hi => hf i hi t))
  rw [h, deriv_sum (fun i hi => hf' i hi t)]

theorem deriv2_affine (a b t : ℝ) :
    deriv (deriv (fun t : ℝ => a + t * b)) t = 0 := by
  have h : deriv (fun t : ℝ => a + t * b) = fun _ => b := by
    funext t
    simpa using ((hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const b)).deriv
  rw [h, deriv_const]

end PaperI
