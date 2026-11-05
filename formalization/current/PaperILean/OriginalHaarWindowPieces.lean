import PaperILean.OriginalHaarWindowEndpoint
import PaperILean.OriginalHaarWindowGluing
import PaperILean.OriginalHaarWindowVariation

/-! The exact compact-piece/endpoint/gluing passage in the original Haar
argument. Actual orbit-format and physical-pivot instantiation are separate. -/
noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped BigOperators

/-- Derivative-sign coefficient bounds and the body majorant imply the
actual relative endpoint bound despite singular endpoint derivatives. -/
theorem originalHaar_analytic_piece_relative_bound
    {ι : Type*} [Fintype ι]
    (g b : ℝ → Fin 6 → ℝ) (q q' : ι → ℝ → ℝ) (a z B H : ℝ)
    (haz : a < z) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hg : ContinuousOn g (Icc a z)) (hb : ContinuousOn b (Ioo a z))
    (hgderiv : ∀ t ∈ Ioo a z,
      HasDerivAt g (originalUpperBodyVelocity (g t) (b t)) t)
    (hqderiv : ∀ i t, t ∈ Ioo a z → HasDerivAt (q i) (q' i t) t)
    (hqcont : ∀ i, ContinuousOn (q' i) (Ioo a z))
    (hqsign : ∀ i, DerivativeSignOn (q i) (Ioo a z))
    (hqrange : ∀ i t, t ∈ Ioo a z → |q i t| ≤ B)
    (hbody : ∀ t ∈ Ioo a z, ∀ i : Fin 6, |b t i| ≤ H*∑ j, |q' j t|) :
    let L : ℝ := H*(Fintype.card ι:ℝ)*(2*B)
    ‖originalUpperRelativeFrame (g a) (g z)‖ ≤ L*(1+L)^2 := by
  dsimp only
  let w : ℝ → ℝ := fun t => H*∑ i, |q' i t|
  have hwc : ContinuousOn w (Ioo a z) := by
    apply continuousOn_const.mul
    exact continuousOn_finset_sum _ (fun i _ => (hqcont i).abs)
  apply originalUpperRelativeFrame_open_piece_bound g b w a z _ haz
    (by positivity) hg hb hgderiv
  · intro u hu v hv huv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact hwc.mono (fun t ht => ⟨hu.1.trans_le ht.1,ht.2.trans_lt hv.2⟩)
  · intro t ht
    exact mul_nonneg hH (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  · exact hbody
  · intro u hu v hv huv
    exact originalHaar_coefficient_body_majorant_integral q q' a z u v B H
      hB hH hu hv huv hqderiv hqcont hqsign hqrange

/-- A fixed number of analytic/sign pieces controls the relative path
endpoint uniformly in the absolute frame. Zero-length pieces are permitted
and require no interior derivatives. -/
theorem originalHaar_piecewise_relative_bound
    {ι : Type*} [Fintype ι]
    (g : ℝ → Fin 6 → ℝ) (b : ℕ → ℝ → Fin 6 → ℝ)
    (q q' : ℕ → ι → ℝ → ℝ) (t : ℕ → ℝ) (n M : ℕ) (B H : ℝ)
    (hn : n ≤ M) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hcuts : ∀ j<n, t j ≤ t (j+1))
    (hg : ∀ j<n, ContinuousOn g (Icc (t j) (t (j+1))))
    (hb : ∀ j<n, ContinuousOn (b j) (Ioo (t j) (t (j+1))))
    (hgderiv : ∀ j<n, ∀ s ∈ Ioo (t j) (t (j+1)),
      HasDerivAt g (originalUpperBodyVelocity (g s) (b j s)) s)
    (hqderiv : ∀ j<n, ∀ i s, s ∈ Ioo (t j) (t (j+1)) →
      HasDerivAt (q j i) (q' j i s) s)
    (hqcont : ∀ j<n, ∀ i, ContinuousOn (q' j i) (Ioo (t j) (t (j+1))))
    (hqsign : ∀ j<n, ∀ i, DerivativeSignOn (q j i) (Ioo (t j) (t (j+1))))
    (hqrange : ∀ j<n, ∀ i s, s ∈ Ioo (t j) (t (j+1)) → |q j i s| ≤ B)
    (hbody : ∀ j<n, ∀ s ∈ Ioo (t j) (t (j+1)), ∀ i : Fin 6,
      |b j s i| ≤ H*∑ l, |q' j l s|) :
    let L : ℝ := H*(Fintype.card ι:ℝ)*(2*B)
    let R : ℝ := L*(1+L)^2
    ‖originalUpperRelativeFrame (g (t 0)) (g (t n))‖+1 ≤ (1+2*R)^M := by
  dsimp only
  let L : ℝ := H*(Fintype.card ι:ℝ)*(2*B)
  let R : ℝ := L*(1+L)^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc := originalUpperRelativeFrame_chain_bound (fun j => g (t j)) n R hR (by
    intro j hj
    rcases (hcuts j hj).eq_or_lt with heq | hlt
    · dsimp only
      rw [heq,originalUpperRelativeFrame_self,norm_zero]
      exact hR
    · exact originalHaar_analytic_piece_relative_bound g (b j) (q j) (q' j)
        (t j) (t (j+1)) B H hlt hB hH (hg j hj) (hb j hj)
        (hgderiv j hj) (hqderiv j hj) (hqcont j hj) (hqsign j hj)
        (hqrange j hj) (hbody j hj))
  exact hc.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1+2*R) hn)

end PaperI
