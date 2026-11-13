import PaperILean.CommonMonotonePartition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The manuscript's derivative-sign argument on actual differentiable pieces.
The sign alternatives refer to the actual derivative. Zero derivative pieces
are retained; their zero sets need not be finite. Constructing a uniformly
bounded analytic/sign subdivision is a separate prerequisite. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

def DerivativeSignOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, 0 < deriv f x) ∨ (∀ x ∈ s, deriv f x < 0) ∨
    (∀ x ∈ s, deriv f x = 0)

theorem monotoneOn_or_antitoneOn_of_derivative_sign
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hs : DerivativeSignOn f (Ioo a b)) :
    MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b) := by
  rcases hs with hp | hn | hz
  · exact Or.inl (strictMonoOn_of_deriv_pos (convex_Ioo a b)
      hf.continuousOn (by simpa only [interior_Ioo] using hp)).monotoneOn
  · exact Or.inr (strictAntiOn_of_deriv_neg (convex_Ioo a b)
      hf.continuousOn (by simpa only [interior_Ioo] using hn)).antitoneOn
  · exact Or.inl (monotoneOn_of_deriv_nonneg (convex_Ioo a b)
      hf.continuousOn (by simpa only [interior_Ioo] using hf)
      (by simpa only [interior_Ioo] using fun x hx => (hz x hx).ge))

theorem constantOn_of_zero_derivative
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hz : ∀ x ∈ Ioo a b, deriv f x = 0) :
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ioo a b) hf.continuousOn
    (by simpa only [interior_Ioo] using hf)
    (by simpa only [interior_Ioo] using fun x hx => (hz x hx).ge)
  have ha := antitoneOn_of_deriv_nonpos (convex_Ioo a b) hf.continuousOn
    (by simpa only [interior_Ioo] using hf)
    (by simpa only [interior_Ioo] using fun x hx => (hz x hx).le)
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact le_antisymm (hm hx hy hxy) (ha hx hy hxy)
  · exact le_antisymm (ha hy hx hyx) (hm hy hx hyx)

theorem closed_monotonicity_of_derivative_sign
    {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hs : DerivativeSignOn f (Ioo a b)) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  rcases hs with hp | hn | hz
  · exact Or.inl (strictMonoOn_of_deriv_pos (convex_Icc a b)
      hc (by simpa only [interior_Icc] using hp)).monotoneOn
  · exact Or.inr (strictAntiOn_of_deriv_neg (convex_Icc a b)
      hc (by simpa only [interior_Icc] using hn)).antitoneOn
  · exact Or.inl (monotoneOn_of_deriv_nonneg (convex_Icc a b)
      hc (by simpa only [interior_Icc] using hf)
      (by simpa only [interior_Icc] using fun x hx => (hz x hx).ge))

theorem monotone_cut_intervals_of_derivative_sign
    (f : ℝ → ℝ) (C : Finset ℝ)
    (hd : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      DifferentiableOn ℝ f (Ioo u v))
    (hs : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      DerivativeSignOn f (Ioo u v)) : MonotoneOnCutIntervals f C := by
  intro u hu v hv huv hgap
  exact monotoneOn_or_antitoneOn_of_derivative_sign
    (hd u hu v hv huv hgap) (hs u hu v hv huv hgap)

/-- The original derivative-sign route to a common partition, with the actual
individual cut bounds retained and no monotonicity premise. -/
theorem common_partition_of_derivative_sign_cuts
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hd : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → DifferentiableOn ℝ (f i) (Ioo u v))
    (hs : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → DerivativeSignOn (f i) (Ioo u v))
    (hcard : ∀ i, (cuts i).card ≤ K i) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ 1 + ∑ i, K i ∧
      t 0 = a ∧ t n = b ∧ MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
        AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
  exact exists_common_monotone_partition_of_card_bounds f cuts K hab ha hb hcuts
    (fun i => monotone_cut_intervals_of_derivative_sign (f i) (cuts i) (hd i) (hs i)) hcard

/-- Each monotone piece contributes at most the original range length. The
analytic/sign cuts and their uniform bounds remain explicit prerequisites. -/
theorem family_variation_le_of_derivative_sign_cuts
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    (K : ι → ℕ) (B : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (hd : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → DifferentiableOn ℝ (f i) (Ioo u v))
    (hs : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → DerivativeSignOn (f i) (Ioo u v))
    (hcard : ∀ i, (cuts i).card ≤ K i)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hB : ∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) :
    ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
      variationOnFromTo (f i) Set.univ a b ≤ ((1 + ∑ k, K k : ℕ) : ℝ) * B i := by
  exact family_variation_le_of_individual_cut_sets f cuts K B hab ha hb hcuts
    (fun i => monotone_cut_intervals_of_derivative_sign (f i) (cuts i) (hd i) (hs i))
    hcard hc hB

theorem monotone_cut_intervals_of_analytic_derivative_sign
    (f : ℝ → ℝ) (C : Finset ℝ)
    (ha : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      AnalyticOnNhd ℝ f (Ioo u v))
    (hs : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      DerivativeSignOn f (Ioo u v)) : MonotoneOnCutIntervals f C := by
  exact monotone_cut_intervals_of_derivative_sign f C
    (fun u hu v hv huv hgap => (ha u hu v hv huv hgap).differentiableOn) hs

/-- This is the original final analytic/sign-subdivision implication. It is
conditional on the actual analytic/sign cut construction, not on monotonicity. -/
theorem family_variation_le_of_analytic_derivative_sign_cuts
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (cuts : ι → Finset ℝ)
    (K : ι → ℕ) (B : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ i, a ∈ cuts i) (hb : ∀ i, b ∈ cuts i)
    (hcuts : ∀ i, ∀ c ∈ cuts i, c ∈ Icc a b)
    (han : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → AnalyticOnNhd ℝ (f i) (Ioo u v))
    (hs : ∀ i, ∀ u ∈ cuts i, ∀ v ∈ cuts i, u < v →
      (∀ c ∈ cuts i, c ∉ Ioo u v) → DerivativeSignOn (f i) (Ioo u v))
    (hcard : ∀ i, (cuts i).card ≤ K i)
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hB : ∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) :
    ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
      variationOnFromTo (f i) Set.univ a b ≤ ((1 + ∑ k, K k : ℕ) : ℝ) * B i := by
  exact family_variation_le_of_derivative_sign_cuts f cuts K B hab ha hb hcuts
    (fun i u hu v hv huv hgap => (han i u hu v hv huv hgap).differentiableOn)
    hs hcard hc hB

end PaperI
