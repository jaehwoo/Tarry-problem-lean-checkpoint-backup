import PaperILean.DerivativeSignSubdivision
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integrate a bounded finite family on its actual analytic/sign pieces,
then pass to the whole open interval. Excluded endpoint values are unused. -/
noncomputable section
namespace PaperI.SectionIntegralCalculus
open Set MeasureTheory Filter
open scoped BigOperators Topology

private theorem signed_piece_abs_deriv_integral
    (q : ℝ → ℝ) (x y B : ℝ) (hxy : x ≤ y) (_hB : 0 ≤ B)
    (hcont : ContinuousOn q (Icc x y))
    (hdiff : DifferentiableOn ℝ q (Ioo x y))
    (hsign : DerivativeSignOn q (Ioo x y))
    (hx : |q x| ≤ B) (hy : |q y| ≤ B) :
    IntervalIntegrable (fun t => |deriv q t|) volume x y ∧
      (∫ t in x..y, |deriv q t|) ≤ 2*B := by
  have hd (t : ℝ) (ht : t ∈ Ioo x y) : HasDerivAt q (deriv q t) t :=
    (hdiff.differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hs : (∀ t ∈ Ioo x y, 0 ≤ deriv q t) ∨
      (∀ t ∈ Ioo x y, deriv q t ≤ 0) := by
    rcases hsign with hp | hn | hz
    · exact Or.inl (fun t ht => (hp t ht).le)
    · exact Or.inr (fun t ht => (hn t ht).le)
    · exact Or.inl (fun t ht => (hz t ht).ge)
  rcases hs with hp | hn
  · have hi : IntervalIntegrable (deriv q) volume x y :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        (by simpa only [uIcc_of_le hxy] using hcont)
        (by simpa only [min_eq_left hxy, max_eq_right hxy] using hd)
        (by simpa only [min_eq_left hxy, max_eq_right hxy] using hp)
    refine ⟨hi.abs, ?_⟩
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hxy hi.abs hi
      (fun t ht => (abs_of_nonneg (hp t ht)).le)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy hcont hd hi] at hm
    have hqx := (abs_le.mp hx).1
    have hqy := (abs_le.mp hy).2
    linarith
  · have hi : IntervalIntegrable (fun t => -deriv q t) volume x y :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        (g := fun t => -q t)
        (by simpa only [uIcc_of_le hxy] using hcont.neg)
        (by simpa only [min_eq_left hxy, max_eq_right hxy] using
          fun t ht => (hd t ht).neg)
        (by simpa only [min_eq_left hxy, max_eq_right hxy] using
          fun t ht => neg_nonneg.mpr (hn t ht))
    have hia : IntervalIntegrable (fun t => |deriv q t|) volume x y := by
      simpa only [abs_neg] using hi.abs
    refine ⟨hia, ?_⟩
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hxy hia hi
      (fun t ht => (abs_of_nonpos (hn t ht)).le)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy hcont.neg
      (fun t ht => (hd t ht).neg) hi] at hm
    have hqx := (abs_le.mp hx).2
    have hqy := (abs_le.mp hy).1
    linarith

private theorem piece_body_integral
    {ι : Type*} [Fintype ι] (q : ι → ℝ → ℝ) (f : ℝ → ℝ)
    (x y A B : ℝ) (hxy : x ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hqcont : ∀ i, ContinuousOn (q i) (Icc x y))
    (hqbound : ∀ i t, t ∈ Icc x y → |q i t| ≤ B)
    (hqsign : ∀ i, DifferentiableOn ℝ (q i) (Ioo x y) ∧
      DerivativeSignOn (q i) (Ioo x y))
    (hfcont : ContinuousOn f (Ioo x y))
    (hfnonneg : ∀ t ∈ Ioo x y, 0 ≤ f t)
    (hmajor : ∀ t ∈ Ioo x y, f t ≤ A * (1 + ∑ i, |deriv (q i) t|)) :
    IntervalIntegrable f volume x y ∧
      (∫ t in x..y, f t) ≤ A * ((y-x) + 2*(Fintype.card ι : ℝ)*B) := by
  classical
  have hi (i : ι) := signed_piece_abs_deriv_integral (q i) x y B hxy hB
    (hqcont i) (hqsign i).1 (hqsign i).2
    (hqbound i x ⟨le_rfl, hxy⟩) (hqbound i y ⟨hxy, le_rfl⟩)
  have hsum : IntervalIntegrable (fun t => ∑ i, |deriv (q i) t|) volume x y := by
    have hs := IntervalIntegrable.sum (f := fun i t => |deriv (q i) t|)
      Finset.univ (fun i _ => (hi i).1)
    have he : (∑ i : ι, fun t => |deriv (q i) t|) =
        (fun t => ∑ i : ι, |deriv (q i) t|) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hs
    exact hs
  have hmaj : IntervalIntegrable (fun t => A * (1 + ∑ i, |deriv (q i) t|))
      volume x y := (intervalIntegrable_const.add hsum).const_mul A
  have hmajopen : IntegrableOn (fun t => A * (1 + ∑ i, |deriv (q i) t|))
      (Ioo x y) := (intervalIntegrable_iff_integrableOn_Ioo_of_le hxy).mp hmaj
  have hfopen : IntegrableOn f (Ioo x y) := hmajopen.mono'
    (hfcont.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_mem measurableSet_Ioo).mono (fun t ht => by
      rw [Real.norm_of_nonneg (hfnonneg t ht)]
      exact hmajor t ht))
  have hfi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hxy).mpr hfopen
  refine ⟨hfi, ?_⟩
  calc
    (∫ t in x..y, f t) ≤ ∫ t in x..y, A * (1 + ∑ i, |deriv (q i) t|) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hxy hfi hmaj hmajor
    _ = A * ((y-x) + ∑ i, (∫ t in x..y, |deriv (q i) t|)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const hsum,
        intervalIntegral.integral_finset_sum (fun i _ => (hi i).1)]
      simp
    _ ≤ A * ((y-x) + ∑ _i : ι, 2*B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_left (Finset.sum_le_sum (fun i _ => (hi i).2)) _) hA
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

private theorem uniform_compact_to_open
    (f : ℝ → ℝ) (a z M : ℝ) (haz : a ≤ z) (hM : 0 ≤ M)
    (hnonneg : ∀ t ∈ Ioo a z, 0 ≤ f t)
    (hcompact : ∀ u v : ℝ, u ≤ v → Icc u v ⊆ Ioo a z →
      IntegrableOn f (Icc u v) ∧ (∫ t in Icc u v, f t) ≤ M) :
    IntegrableOn f (Ioo a z) ∧ (∫ t in Ioo a z, f t) ≤ M := by
  by_cases heq : a = z
  · subst z
    simpa using hM
  have hlt : a < z := lt_of_le_of_ne haz heq
  obtain ⟨u,v,_huanti,_hvmono,hu,hv,huv,hua,hvz⟩ :=
    exists_seq_strictAnti_strictMono_tendsto hlt
  have hsub (n : ℕ) : Icc (u n) (v n) ⊆ Ioo a z := fun t ht =>
    ⟨(hu n).1.trans_le ht.1, ht.2.trans_lt (hv n).2⟩
  have hc (n : ℕ) := hcompact (u n) (v n) (huv n n).le (hsub n)
  have hcover : AECover (volume.restrict (Ioo a z)) atTop
      (fun n : ℕ => Icc (u n) (v n)) := aecover_Ioo_of_Icc hua hvz
  have hi (n : ℕ) : IntegrableOn f (Icc (u n) (v n))
      (volume.restrict (Ioo a z)) := by
    change Integrable f ((volume.restrict (Ioo a z)).restrict (Icc (u n) (v n)))
    rw [Measure.restrict_restrict_of_subset (hsub n)]
    exact (hc n).1
  have hb : ∀ᶠ n : ℕ in atTop,
      (∫ t in Icc (u n) (v n), f t ∂volume.restrict (Ioo a z)) ≤ M :=
    Eventually.of_forall (fun n => by
      rw [Measure.restrict_restrict_of_subset (hsub n)]
      exact (hc n).2)
  have hn : ∀ᵐ t ∂volume.restrict (Ioo a z), 0 ≤ f t :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun t ht => hnonneg t ht)
  have hall := hcover.integrable_of_integral_bounded_of_nonneg_ae M hi hn hb
  exact ⟨hall, le_of_tendsto (hcover.integral_tendsto_of_countably_generated hall) hb⟩

/-- Actual nonnegative body integrands controlled on common analytic/sign gaps
are integrable on the whole open interval. The cut bound is uniform before
the compact endpoints; no endpoint derivative or endpoint continuity is used. -/
theorem bounded_sign_family_body_integral
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ → ℝ) (f : ℝ → ℝ) (a z A B : ℝ) (K : ℕ)
    (haz : a ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hqcont : ∀ i, ContinuousOn (q i) (Ioo a z))
    (hqbound : ∀ i t, t ∈ Ioo a z → |q i t| ≤ B)
    (hnonneg : ∀ t ∈ Ioo a z, 0 ≤ f t)
    (hcuts : ∀ u v : ℝ, u ≤ v → Icc u v ⊆ Ioo a z →
      ∃ C : Finset ℝ, u ∈ C ∧ v ∈ C ∧
        (∀ c ∈ C, c ∈ Icc u v) ∧ C.card ≤ K ∧
        ∀ x ∈ C, ∀ y ∈ C, x < y →
          (∀ c ∈ C, c ∉ Ioo x y) →
          (∀ i, AnalyticOnNhd ℝ (q i) (Ioo x y) ∧
            DerivativeSignOn (q i) (Ioo x y)) ∧
          ContinuousOn f (Ioo x y) ∧
          (∀ t ∈ Ioo x y, f t ≤ A * (1 + ∑ i, |deriv (q i) t|))) :
    IntegrableOn f (Ioo a z) ∧
      (∫ t in Ioo a z, f t) ≤
        A * ((z-a) + 2 * (K : ℝ) * (Fintype.card ι : ℝ) * B) := by
  classical
  apply uniform_compact_to_open f a z _ haz
    (mul_nonneg hA (add_nonneg (sub_nonneg.mpr haz) (by positivity))) hnonneg
  intro u v huv huvsub
  obtain ⟨C,hu,hv,hC,hcard,hprops⟩ := hcuts u v huv huvsub
  obtain ⟨n,t,hn,ht0,htn,ht,hgap⟩ := exists_sorted_cut_partition C hu hv hC
  have hnK : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show n ≤ K by omega)
  have hpiece (j : ℕ) (hj : j < n) :
      IntervalIntegrable f volume (t j) (t (j+1)) ∧
      (∫ s in (t j)..(t (j+1)), f s) ≤
        A * ((t (j+1)-t j) + 2*(Fintype.card ι : ℝ)*B) := by
    obtain ⟨hx,hy,hxy,hno⟩ := hgap j hj
    obtain ⟨hqs,hfc,hfm⟩ := hprops (t j) hx (t (j+1)) hy hxy hno
    have hsub : Icc (t j) (t (j+1)) ⊆ Ioo a z :=
      fun s hs => huvsub ⟨(hC _ hx).1.trans hs.1, hs.2.trans (hC _ hy).2⟩
    exact piece_body_integral q f (t j) (t (j+1)) A B hxy.le hA hB
      (fun i => (hqcont i).mono hsub) (fun i s hs => hqbound i s (hsub hs))
      (fun i => ⟨(hqs i).1.differentiableOn, (hqs i).2⟩) hfc
      (fun s hs => hnonneg s (hsub (Ioo_subset_Icc_self hs))) hfm
  have hfi : IntervalIntegrable f volume u v := by
    simpa only [ht0,htn] using IntervalIntegrable.trans_iterate
      (fun j hj => (hpiece j hj).1)
  have hlength : ∑ j ∈ Finset.range n, (t (j+1)-t j) = v-u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := t) (n := n) (μ := volume) (f := fun _ : ℝ => (1 : ℝ))
      (fun _ _ => intervalIntegrable_const)
    simpa [ht0,htn] using h
  have hbound : (∫ s in u..v, f s) ≤
      A * ((v-u) + 2*(n : ℝ)*(Fintype.card ι : ℝ)*B) := by
    calc
      _ = ∑ j ∈ Finset.range n, ∫ s in (t j)..(t (j+1)), f s := by
        simpa only [ht0,htn] using
          (intervalIntegral.sum_integral_adjacent_intervals (fun j hj => (hpiece j hj).1)).symm
      _ ≤ ∑ j ∈ Finset.range n, A * ((t (j+1)-t j) + 2*(Fintype.card ι : ℝ)*B) :=
        Finset.sum_le_sum (fun j hj => (hpiece j (Finset.mem_range.mp hj)).2)
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hlength]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hends : v-u ≤ z-a := by
    have hu' := huvsub (show u ∈ Icc u v from ⟨le_rfl,huv⟩)
    have hv' := huvsub (show v ∈ Icc u v from ⟨huv,le_rfl⟩)
    linarith [hu'.1,hv'.2]
  have hfinal : (∫ s in u..v, f s) ≤
      A * ((z-a) + 2*(K : ℝ)*(Fintype.card ι : ℝ)*B) :=
    hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hends
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnK (by norm_num)) (Nat.cast_nonneg _)) hB)) hA)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hfi, ?_⟩
  simpa only [intervalIntegral.integral_of_le huv, integral_Icc_eq_integral_Ioc] using hfinal

end PaperI.SectionIntegralCalculus
