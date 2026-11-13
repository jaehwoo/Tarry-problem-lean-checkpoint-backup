import PaperILean.OriginalPreparationFiniteList
import PaperILean.PreparationGoodComponents

/-! Positive-order preparation and bounded open-component bookkeeping for
I932-I948. Zero-order level sets are never assumed semialgebraic. -/
noncomputable section
namespace PaperI.Preparation
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem positive_order_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ι → ℝ → ℝ) (B : ι → ℝ) (a b : ℝ),
      a < b → (∀ i, 0 ≤ B i) →
      (∀ i, ContDiffOn ℝ N (f i) (Ioo a b)) →
      (∀ i, ∀ x ∈ Ioo a b, |f i x| ≤ B i) →
      (∀ i, ∀ n, 0 < n → n ≤ N → ∀ threshold sign : ℝ, |sign| = 1 →
        Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel (f i) n a b threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel (f i) n a b threshold sign)) ≤ K) →
      ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ioo a b ∧
        volume (Ioo a b \ G) ≤ ENNReal.ofReal (ε * (b-a)) ∧
        ∀ x ∈ G, ∀ i, ∀ n ≤ N, |iteratedDeriv n (f i) x| ≤ C * B i / (b-a)^n := by
  classical
  let den : ℝ := 2 * ((K : ℝ)+1) * ((N : ℝ)+1) * ((Fintype.card ι : ℝ)+1)
  have hden : 0 < den := by dsimp [den]; positivity
  let δ : ℝ := ε / den
  have hδ : 0 < δ := div_pos hε hden
  let c : Fin (N+1) → ℝ := fun j => (4 * (j.val : ℝ) / δ)^j.val
  have hc : ∀ j, 0 ≤ c j := by intro j; dsimp [c]; positivity
  let C : ℝ := 1 + ∑ j, c j
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hc j)
  have hCj : ∀ j : Fin (N+1), (4 * (j.val : ℝ) / δ)^j.val ≤ C := by
    intro j
    have hj := Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ j)
    change c j ≤ C
    dsimp [C]
    linarith
  refine ⟨C,hC1,?_⟩
  intro f B a b hab hB hsmooth hamp hcount
  have hL : 0 < b-a := sub_pos.mpr hab
  let E : ι × Fin (N+1) → Set ℝ := fun k =>
    {x | x ∈ Ioo a b ∧ C * B k.1 / (b-a)^k.2.val < |iteratedDeriv k.2.val (f k.1) x|}
  let budget : ℝ := 2 * (K : ℝ) * δ * (b-a)
  have hbudget : 0 ≤ budget := by dsimp [budget]; positivity
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    exact ((continuousOn_iteratedDeriv_of_contDiffOn_Ioo (hsmooth k.1)
      (Nat.lt_succ_iff.mp k.2.isLt)).abs.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi).measurableSet
  have hE : ∀ k, volume (E k) ≤ ENNReal.ofReal budget := by
    intro k
    by_cases hk : k.2.val = 0
    · have he : E k = ∅ := by
        ext x
        simp only [E, hk, iteratedDeriv_zero, pow_zero, div_one, mem_setOf_eq,
          mem_empty_iff_false, iff_false]
        rintro ⟨hx,hbad⟩
        have hm := hamp k.1 x hx
        have hmul : B k.1 ≤ C * B k.1 := by nlinarith [hB k.1]
        exact (not_lt_of_ge (hm.trans hmul)) hbad
      rw [he, measure_empty]
      exact bot_le
    · exact published_abs_derivative_superlevel_volume_le hDD k.2.val N K (f k.1)
        a b (B k.1) δ C (Nat.pos_of_ne_zero hk) (Nat.lt_succ_iff.mp k.2.isLt)
        hab (hB k.1) hδ (hCj k.2) (hsmooth k.1) (hamp k.1)
        (fun sign hsign => hcount k.1 k.2.val (Nat.pos_of_ne_zero hk) (Nat.lt_succ_iff.mp k.2.isLt) _ sign hsign)
  obtain ⟨G,hGm,hGsub,hGbad,hGood⟩ := preparation_common_measurable_good_set
    volume (Ioo a b) measurableSet_Ioo Finset.univ E (fun k _ => hEm k)
    (fun k x => |iteratedDeriv k.2.val (f k.1) x| ≤ C * B k.1 / (b-a)^k.2.val)
    (fun _ => budget) (fun _ _ => hbudget) (fun k _ => hE k)
    (fun k _ x hx hnot => le_of_not_gt (fun hlt => hnot ⟨hx,hlt⟩))
  have hcoef : 2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ) ≤ den := by
    dsimp [den]
    gcongr <;> linarith
  have hscaled : (2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ)) * δ ≤ ε := by
    calc
      _ ≤ den * δ := mul_le_mul_of_nonneg_right hcoef hδ.le
      _ = ε := by dsimp [δ]; field_simp [ne_of_gt hden]
  have htotal : (∑ _k : ι × Fin (N+1), budget) ≤ ε * (b-a) := by
    calc
      _ = (2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ)) * δ * (b-a) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, budget]
        ring
      _ ≤ ε * (b-a) := mul_le_mul_of_nonneg_right hscaled (sub_nonneg.mpr hab.le)
  refine ⟨G,hGm,hGsub,hGbad.trans (ENNReal.ofReal_le_ofReal htotal),?_⟩
  intro x hx i n hn
  exact hGood x hx (i,⟨n,Nat.lt_succ_iff.mpr hn⟩) (Finset.mem_univ _)


/-- A subset of a bounded open set is controlled by uniform budgets on its
actual component intervals. No measurable endpoint choice is involved. -/
theorem volume_subset_component_budget {U E : Set ℝ} {a b c : ℝ} {K : ℕ}
    (ho : IsOpen U) (hsub : U ⊆ Ioo a b) (hE : E ⊆ U)
    [Finite (ConnectedComponents U)] (hK : Nat.card (ConnectedComponents U) ≤ K)
    (hc : 0 ≤ c)
    (hpart : ∀ u v : ℝ, a ≤ u → u < v → v ≤ b → Ioo u v ⊆ U →
      volume (E ∩ Ioo u v) ≤ ENNReal.ofReal c) :
    volume E ≤ ENNReal.ofReal ((K : ℝ) * c) := by
  classical
  letI := Fintype.ofFinite (ConnectedComponents U)
  obtain ⟨l,r,hparts,hcover⟩ := open_set_component_intervals ho hsub
  have he : E ⊆ ⋃ i, E ∩ Ioo (l i) (r i) := by
    intro x hx
    have hu := hE hx
    rw [hcover] at hu
    obtain ⟨i,hi⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨i,hx,hi⟩
  calc
    volume E ≤ volume (⋃ i, E ∩ Ioo (l i) (r i)) := measure_mono he
    _ ≤ ∑ i, volume (E ∩ Ioo (l i) (r i)) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _i : ConnectedComponents U, ENNReal.ofReal c := by
      apply Finset.sum_le_sum
      intro i _
      exact hpart (l i) (r i) (hparts i).1 (hparts i).2.1
        (hparts i).2.2.1 (hparts i).2.2.2
    _ = (Nat.card (ConnectedComponents U) : ℝ≥0∞) * ENNReal.ofReal c := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (K : ℝ≥0∞) * ENNReal.ofReal c := by
      exact mul_le_mul_right' (by exact_mod_cast hK) _
    _ = ENNReal.ofReal ((K : ℝ) * c) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]

/-- Scaling from a retained component to the ambient side length. -/
theorem component_threshold_le {δ L ell C D B : ℝ} (n : ℕ)
    (hδ : 0 < δ) (hL : 0 < L) (hsize : δ * L ≤ ell)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : (1/δ)^n ≤ D) :
    C * B / ell^n ≤ (C * D) * B / L^n := by
  have hdL : 0 < δ * L := mul_pos hδ hL
  have hell : 0 < ell := hdL.trans_le hsize
  have hrec : 1 / ell^n ≤ D / L^n := by
    calc
      1 / ell^n ≤ 1 / (δ * L)^n :=
        one_div_le_one_div_of_le (pow_pos hdL n) (pow_le_pow_left₀ hdL.le hsize n)
      _ = (1/δ)^n / L^n := by rw [mul_pow, div_pow]; ring
      _ ≤ D / L^n := div_le_div_of_nonneg_right hD (pow_nonneg hL.le n)
  have h := mul_le_mul_of_nonneg_left hrec (mul_nonneg hC hB)
  convert h using 1 <;> ring

/-- Preparation on a bounded open set at the ambient interval scale.
Short components are charged to the exceptional budget, never assumed absent.
Only positive-order derivative superlevel component counts are retained. -/
theorem open_component_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N KU KD : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ι → ℝ → ℝ) (B : ι → ℝ)
      (a b : ℝ) (U : Set ℝ), a < b → IsOpen U → U ⊆ Ioo a b →
      Finite (ConnectedComponents U) → Nat.card (ConnectedComponents U) ≤ KU →
      (∀ i, 0 ≤ B i) → (∀ i, ContDiffOn ℝ N (f i) U) →
      (∀ i, ∀ x ∈ U, |f i x| ≤ B i) →
      (∀ u v, a ≤ u → u < v → v ≤ b → Ioo u v ⊆ U →
        ∀ i, ∀ n, 0 < n → n ≤ N → ∀ threshold sign : ℝ, |sign| = 1 →
          Finite (ConnectedComponents
            (signedIteratedDerivativeSuperlevel (f i) n u v threshold sign)) ∧
          Nat.card (ConnectedComponents
            (signedIteratedDerivativeSuperlevel (f i) n u v threshold sign)) ≤ KD) →
      volume {x | x ∈ U ∧ ∃ i, ∃ n ≤ N,
        C * B i / (b-a)^n < |iteratedDeriv n (f i) x|} ≤
        ENNReal.ofReal (ε * (b-a)) := by
  classical
  let δ : ℝ := ε / ((KU : ℝ)+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨C0,hC0,hprep⟩ := positive_order_preparation (ι := ι) hDD N KD δ hδ
  let D : ℝ := 1 + ∑ n : Fin (N+1), (1/δ)^n.val
  have hD1 : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity))
  have hDn (n : ℕ) (hn : n ≤ N) : (1/δ)^n ≤ D := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (N+1))))
      (f := fun q => (1/δ)^q.val) (fun _ _ => by positivity)
      (Finset.mem_univ (⟨n,Nat.lt_succ_iff.mpr hn⟩ : Fin (N+1)))
    dsimp [D]
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C0*D,one_le_mul_of_one_le_of_one_le hC0 hD1,?_⟩
  intro f B a b U hab ho hsub hfinite hKU hB hsmooth hamp hcount
  letI := hfinite
  let E := {x | x ∈ U ∧ ∃ i, ∃ n ≤ N,
    (C0*D) * B i / (b-a)^n < |iteratedDeriv n (f i) x|}
  have hL : 0 < b-a := sub_pos.mpr hab
  have hbudget := volume_subset_component_budget (E := E) ho hsub
    (fun _ hx => hx.1) hKU (mul_nonneg hδ.le hL.le) (fun u v hau huv hvb hU => by
      have hlen : v-u ≤ b-a := by linarith
      by_cases hshort : v-u ≤ δ*(b-a)
      · exact (measure_mono inter_subset_right).trans
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal hshort)
      · obtain ⟨G,hGm,hGsub,hGbad,hGood⟩ := hprep f B u v huv hB
          (fun i => (hsmooth i).mono hU) (fun i x hx => hamp i x (hU hx))
          (hcount u v hau huv hvb hU)
        have hEG : E ∩ Ioo u v ⊆ Ioo u v \ G := by
          intro x hx
          refine ⟨hx.2,?_⟩
          intro hg
          obtain ⟨i,n,hn,hbad⟩ := hx.1.2
          have hloc := hGood x hg i n hn
          have hscale := component_threshold_le n hδ hL (le_of_not_ge hshort)
            (zero_le_one.trans hC0) (hB i) (hDn n hn)
          exact (not_lt_of_ge (hloc.trans hscale)) hbad
        exact (measure_mono hEG).trans (hGbad.trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlen hδ.le))))
  have hcoef : (KU : ℝ)*δ ≤ ε := by
    have hden : 0 < (KU : ℝ)+1 := by positivity
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact hbudget.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

end PaperI.Preparation
