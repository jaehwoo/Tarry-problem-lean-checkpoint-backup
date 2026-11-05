import PaperILean.FinitePieceFTC
import PaperILean.OriginalHaarWindowPivot
import PaperILean.FiniteMonotoneVariation

/-! Quantitative finite-sign variation and integrals, including singular
endpoints. These are used for the actual fixed-d path stage I3237[0,119). -/
noncomputable section
namespace PaperI.FiniteSignIntegralBounds
open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem signed_piece_integral (q : ℝ → ℝ) (a z B : ℝ) (haz : a ≤ z)
    (hc : ContinuousOn q (Icc a z)) (hd : DifferentiableOn ℝ q (Ioo a z))
    (hs : DerivativeSignOn q (Ioo a z)) (ha : |q a| ≤ B) (hz : |q z| ≤ B) :
    IntervalIntegrable (fun t => |deriv q t|) volume a z ∧
      (∫ t in a..z, |deriv q t|) ≤ 2*B := by
  have hder t (ht : t ∈ Ioo a z) : HasDerivAt q (deriv q t) t :=
    (hd.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hi := FinitePieceFTC.signed_derivative_integrable q (deriv q) a z haz hc hder hs
  refine ⟨hi.abs,?_⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le haz hc hder hi
  have hsign : (∀ t ∈ Ioo a z, 0 ≤ deriv q t) ∨
      (∀ t ∈ Ioo a z, deriv q t ≤ 0) := by
    rcases hs with hp | hn | hzero
    · exact Or.inl (fun t ht => (hp t ht).le)
    · exact Or.inr (fun t ht => (hn t ht).le)
    · exact Or.inl (fun t ht => (hzero t ht).ge)
  rcases hsign with hp | hn
  · have hm := intervalIntegral.integral_mono_on_of_le_Ioo haz hi.abs hi
      (fun t ht => (abs_of_nonneg (hp t ht)).le)
    rw [hftc] at hm
    linarith [(abs_le.mp ha).1,(abs_le.mp hz).2]
  · have hm := intervalIntegral.integral_mono_on_of_le_Ioo haz hi.abs hi.neg
      (fun t ht => (abs_of_nonpos (hn t ht)).le)
    change (∫ t in a..z, |deriv q t|) ≤ ∫ t in a..z, -(deriv q t) at hm
    rw [intervalIntegral.integral_neg,hftc] at hm
    linarith [(abs_le.mp ha).2,(abs_le.mp hz).1]

/-- Both variation and the absolute derivative integral use the same finite
cut count. No derivative at any cut is required. -/
theorem scalar_cut_bounds (q : ℝ → ℝ) (C : Finset ℝ) (a z B : ℝ) (K : ℕ)
    (ha : a ∈ C) (hz : z ∈ C) (hC : ∀ c ∈ C, c ∈ Icc a z) (hK : C.card ≤ K)
    (hB : 0 ≤ B) (hc : ContinuousOn q (Icc a z))
    (hb : ∀ t ∈ Icc a z, |q t| ≤ B)
    (hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      DifferentiableOn ℝ q (Ioo u v) ∧ DerivativeSignOn q (Ioo u v)) :
    BoundedVariationOn q (Icc a z) ∧
      variationOnFromTo q univ a z ≤ 2*(K:ℝ)*B ∧
      IntervalIntegrable (fun t => |deriv q t|) volume a z ∧
      (∫ t in a..z, |deriv q t|) ≤ 2*(K:ℝ)*B := by
  classical
  obtain ⟨n,t,hn,ht0,htn,ht,hgap⟩ := exists_sorted_cut_partition C ha hz hC
  have hnK : (n:ℝ) ≤ K := by exact_mod_cast (show n ≤ K by omega)
  have hpiece (j : ℕ) (hj : j<n) := hgap j hj
  have hv := real_variation_le_of_finite_monotone_partition q t n ht
    (fun j hj => by
      obtain ⟨hu,hv,huv,hno⟩ := hpiece j hj
      have hh := hp (t j) hu (t (j+1)) hv huv hno
      exact closed_monotonicity_of_derivative_sign
        (hc.mono (Icc_subset_Icc (hC _ hu).1 (hC _ hv).2)) hh.1 hh.2)
    (2*B) (by
      intro x hx y hy
      rw [ht0,htn] at hx hy
      exact (abs_sub (q x) (q y)).trans (by linarith [hb x hx,hb y hy]))
  rw [ht0,htn] at hv
  have hib (j : ℕ) (hj : j<n) :
      IntervalIntegrable (fun t => |deriv q t|) volume (t j) (t (j+1)) ∧
      (∫ r in (t j)..(t (j+1)), |deriv q r|) ≤ 2*B := by
    obtain ⟨hu,hv,huv,hno⟩ := hpiece j hj
    have hh := hp (t j) hu (t (j+1)) hv huv hno
    exact signed_piece_integral q _ _ B huv.le
      (hc.mono (Icc_subset_Icc (hC _ hu).1 (hC _ hv).2)) hh.1 hh.2
      (hb _ (hC _ hu)) (hb _ (hC _ hv))
  have hsize : (n:ℝ)*(2*B) ≤ 2*(K:ℝ)*B := by nlinarith
  refine ⟨hv.1,hv.2.trans hsize,?_,?_⟩
  · simpa only [ht0,htn] using IntervalIntegrable.trans_iterate (fun j hj => (hib j hj).1)
  · calc
      _ = ∑ j ∈ Finset.range n, ∫ r in (t j)..(t (j+1)), |deriv q r| := by
        simpa only [ht0,htn] using
          (intervalIntegral.sum_integral_adjacent_intervals (fun j hj => (hib j hj).1)).symm
      _ ≤ ∑ _j ∈ Finset.range n, 2*B :=
        Finset.sum_le_sum (fun j hj => (hib j (Finset.mem_range.mp hj)).2)
      _ = (n:ℝ)*(2*B) := by simp
      _ ≤ _ := hsize

/-- Euclidean partition length is bounded by the sum of the genuine finite
coordinate variations. Finiteness is explicit before taking `toReal`. -/
theorem euclidean_partition_le_variation {ι : Type*} [Fintype ι]
    (q : ι → ℝ → ℝ) (a z : ℝ) (haz : a ≤ z)
    (hbv : ∀ i, BoundedVariationOn (q i) (Icc a z))
    (n : ℕ) (t : ℕ → ℝ) (ht : MonotoneOn t (Icc 0 n))
    (hr : ∀ j ∈ Icc 0 n, t j ∈ Icc a z) :
    (∑ j ∈ Finset.range n, coordinateL2Norm (fun i => q i (t (j+1))-q i (t j))) ≤
      ∑ i, variationOnFromTo (q i) univ a z := by
  classical
  have hs (i : ι) : (∑ j ∈ Finset.range n, |q i (t (j+1))-q i (t j)|) ≤
      variationOnFromTo (q i) univ a z := by
    have he := eVariationOn.sum_le_of_monotoneOn_Icc (q i) ht hr
    have hre := ENNReal.toReal_mono (hbv i) he
    rw [variationOnFromTo.eq_of_le (q i) univ haz,univ_inter]
    simpa only [Nat.Ico_zero_eq_range,ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _),
      ← dist_edist,Real.dist_eq] using hre
  calc
    _ ≤ ∑ j ∈ Finset.range n, ∑ i, |q i (t (j+1))-q i (t j)| :=
      Finset.sum_le_sum (fun j _ => originalHaar_coordinateL2Norm_le_sum_abs _)
    _ = ∑ i, ∑ j ∈ Finset.range n, |q i (t (j+1))-q i (t j)| := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hs i)

theorem coordinate_norm_integrable {ι : Type*} [Fintype ι]
    (f : ℝ → ι → ℝ) (a z : ℝ)
    (hi : ∀ i, IntervalIntegrable (fun t => f t i) volume a z) :
    IntervalIntegrable (fun t => coordinateL2Norm (f t)) volume a z := by
  classical
  have hs : IntervalIntegrable (fun t => ∑ i, |f t i|) volume a z := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => (hi i).abs)
    have he : (∑ i, fun t => |f t i|) = (fun t => ∑ i, |f t i|) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hm : AEStronglyMeasurable (fun t => coordinateL2Norm (f t))
      (volume.restrict (uIoc a z)) := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    exact Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hi i).def'.aestronglyMeasurable.pow 2)
  apply hs.mono_fun' hm
  exact Eventually.of_forall (fun t => by
    change ‖coordinateL2Norm (f t)‖ ≤ ∑ i, |f t i|
    rw [Real.norm_of_nonneg (coordinateL2Norm_nonneg _)]
    exact originalHaar_coordinateL2Norm_le_sum_abs _)

/-- Finite singular sets have no effect on an inequality between integrals. -/
theorem integral_mono_off_cuts (f g : ℝ → ℝ) (C : Finset ℝ) (a z : ℝ)
    (haz : a ≤ z) (ha : a ∈ C) (hz : z ∈ C)
    (hf : IntervalIntegrable f volume a z) (hg : IntervalIntegrable g volume a z)
    (h : ∀ t ∈ Ioo a z, t ∉ C → f t ≤ g t) :
    (∫ t in a..z, f t) ≤ ∫ t in a..z, g t := by
  apply intervalIntegral.integral_mono_ae_restrict haz hf hg
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    C.finite_toSet.countable.ae_not_mem (volume.restrict (Icc a z))] with t ht hn
  have hta : a < t := lt_of_le_of_ne ht.1 (by intro he; exact hn (he ▸ ha))
  have htz : t < z := lt_of_le_of_ne ht.2 (by intro he; exact hn (he.symm ▸ hz))
  exact h t ⟨hta,htz⟩ hn

end PaperI.FiniteSignIntegralBounds
