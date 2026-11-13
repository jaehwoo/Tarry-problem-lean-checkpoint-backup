import PaperILean.PreparationOpenComponents
import PaperILean.PreparationMixedJets
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff
namespace PaperI.Preparation

/-- Fubini with a uniform vertical section budget. -/
theorem rectangle_section_budget {E : Set (ℝ × ℝ)} {a b q : ℝ}
    (hm : MeasurableSet E) (hsub : E ⊆ Ioo a b ×ˢ univ)
    (hsec : ∀ x ∈ Ioo a b, volume (Prod.mk x ⁻¹' E) ≤ ENNReal.ofReal q) :
    volume E ≤ ENNReal.ofReal q * ENNReal.ofReal (b-a) := by
  classical
  change (volume.prod volume) E ≤ _
  rw [Measure.prod_apply hm]
  calc
    _ ≤ ∫⁻ x, (Ioo a b).indicator (fun _ => ENNReal.ofReal q) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Ioo a b
      · simpa only [indicator_of_mem hx] using hsec x hx
      · have he : Prod.mk x ⁻¹' E = ∅ := by
          ext y
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          exact fun h => hx (hsub h).1
        simpa only [he, measure_empty] using (bot_le : (0 : ℝ≥0∞) ≤ _)
    _ = _ := by rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]

/-- The same estimate with horizontal sections. -/
theorem rectangle_section_budget_swap {E : Set (ℝ × ℝ)} {a b q : ℝ}
    (hm : MeasurableSet E) (hsub : E ⊆ univ ×ˢ Ioo a b)
    (hsec : ∀ y ∈ Ioo a b, volume ((fun x => (x,y)) ⁻¹' E) ≤ ENNReal.ofReal q) :
    volume E ≤ ENNReal.ofReal q * ENNReal.ofReal (b-a) := by
  classical
  change (volume.prod volume) E ≤ _
  rw [Measure.prod_apply_symm hm]
  calc
    _ ≤ ∫⁻ y, (Ioo a b).indicator (fun _ => ENNReal.ofReal q) y := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ Ioo a b
      · simpa only [indicator_of_mem hy] using hsec y hy
      · have he : (fun x => (x,y)) ⁻¹' E = ∅ := by
          ext x
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          exact fun h => hy (hsub h).2
        simpa only [he, measure_empty] using (bot_le : (0 : ℝ≥0∞) ≤ _)
    _ = _ := by rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]

def horizontalGood {ι : Type*} (f : ι → ℝ × ℝ → ℝ) (B : ι → ℝ)
    (N : ℕ) (C x0 x1 y0 y1 : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1 ∧ ∀ i (a : Fin (N+1)),
    0 < a.val → 0 < B i → |horizontalJet (f i) a.val p| < C * B i / (x1-x0)^a.val}

theorem isOpen_horizontalGood {ι : Type*} [Fintype ι]
    {f : ι → ℝ × ℝ → ℝ} {B : ι → ℝ} {N : ℕ} {C x0 x1 y0 y1 : ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo x0 x1 ×ˢ Ioo y0 y1)) :
    IsOpen (horizontalGood f B N C x0 x1 y0 y1) := by
  classical
  let R := Ioo x0 x1 ×ˢ Ioo y0 y1
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have he : horizontalGood f B N C x0 x1 y0 y1 =
      R ∩ ⋂ i, ⋂ a : Fin (N+1),
        (if 0 < a.val ∧ 0 < B i then
          R ∩ {p | |horizontalJet (f i) a.val p| < C * B i / (x1-x0)^a.val}
        else univ) := by
    ext p
    simp only [horizontalGood, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_univ, and_true]
    constructor
    · rintro ⟨hp,hh⟩
      refine ⟨hp,?_⟩
      intro i a
      split_ifs with h
      · exact ⟨hp,hh i a h.1 h.2⟩
      · trivial
    · rintro ⟨hp,hh⟩
      refine ⟨hp,?_⟩
      intro i a ha hB
      have := hh i a
      rw [if_pos ⟨ha,hB⟩] at this
      exact this.2
  rw [he]
  apply hR.inter
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro a
  split_ifs
  · exact ((continuousOn_horizontalJet hR (hf i) a.val).abs.isOpen_inter_preimage hR isOpen_Iio)
  · exact isOpen_univ

/-- Horizontal preparation is a literal open derivative-inequality set,
so Fubini does not require a measurable choice of one-dimensional witnesses. -/
theorem horizontalGood_volume
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ι → ℝ × ℝ → ℝ) (B : ι → ℝ)
      (x0 x1 y0 y1 : ℝ), x0 < x1 → y0 < y1 → (∀ i, 0 ≤ B i) →
      (∀ i, ContDiffOn ℝ ∞ (f i) (Ioo x0 x1 ×ˢ Ioo y0 y1)) →
      (∀ i p, p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1 → |f i p| ≤ B i) →
      (∀ y ∈ Ioo y0 y1, ∀ i n, 0 < n → n ≤ N →
        ∀ threshold sign : ℝ, |sign| = 1 →
        Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel
          (fun x => f i (x,y)) n x0 x1 threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel
          (fun x => f i (x,y)) n x0 x1 threshold sign)) ≤ K) →
      volume ((Ioo x0 x1 ×ˢ Ioo y0 y1) \ horizontalGood f B N C x0 x1 y0 y1)
        ≤ ENNReal.ofReal (ε * (x1-x0) * (y1-y0)) := by
  classical
  obtain ⟨C0,hC0,hprep⟩ := positive_order_preparation hDD (ι := ι) N K ε hε
  refine ⟨2*C0, by linarith, ?_⟩
  intro f B x0 x1 y0 y1 hx hy hB hf hamp hcount
  have hL : 0 < x1-x0 := sub_pos.mpr hx
  have hG := isOpen_horizontalGood (B := B) (N := N) (C := 2*C0) hf
  have hh := rectangle_section_budget_swap
    (E := (Ioo x0 x1 ×ˢ Ioo y0 y1) \ horizontalGood f B N (2*C0) x0 x1 y0 y1)
    ((isOpen_Ioo.prod isOpen_Ioo).measurableSet.diff hG.measurableSet)
    (fun p hp => ⟨mem_univ _,hp.1.2⟩) (q := ε*(x1-x0)) (a := y0) (b := y1) ?_
  · exact hh.trans_eq (by rw [← ENNReal.ofReal_mul (mul_nonneg hε.le hL.le)])
  intro y hy'
  obtain ⟨G,hGm,hGsub,hGbad,hGood⟩ := hprep (fun i x => f i (x,y)) B x0 x1 hx hB
    (fun i => (contDiffOn_sectionX (hf i) hy').of_le (by exact_mod_cast (show (N : ℕ∞) ≤ ⊤ from le_top)))
    (fun i x hx' => hamp i (x,y) ⟨hx',hy'⟩) (hcount y hy')
  apply (measure_mono ?_).trans hGbad
  intro x hp
  refine ⟨hp.1.1,?_⟩
  intro hxG
  apply hp.2
  refine ⟨⟨hp.1.1,hy'⟩,?_⟩
  intro i a ha hBi
  rw [horizontalJet_eq_iteratedDeriv]
  have hbound := hGood x hxG i a.val (Nat.lt_succ_iff.mp a.isLt)
  have hpos : 0 < C0 * B i / (x1-x0)^a.val := by positivity
  have he : 2*C0*B i/(x1-x0)^a.val = 2*(C0*B i/(x1-x0)^a.val) := by ring
  rw [he]
  linarith

def horizontalCounts {ι : Type*} (f : ι → ℝ × ℝ → ℝ)
    (N K : ℕ) (x0 x1 y0 y1 : ℝ) : Prop :=
  ∀ y ∈ Ioo y0 y1, ∀ i n, 0 < n → n ≤ N → ∀ threshold sign : ℝ, |sign| = 1 →
    Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel
      (fun x => f i (x,y)) n x0 x1 threshold sign)) ∧
    Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel
      (fun x => f i (x,y)) n x0 x1 threshold sign)) ≤ K

def verticalCounts {ι : Type*} (f : ι → ℝ × ℝ → ℝ)
    (N K : ℕ) (x0 x1 y0 y1 : ℝ) : Prop :=
  ∀ x ∈ Ioo x0 x1, ∀ a b, 0 < b → a+b ≤ N →
    ∀ u v, y0 ≤ u → u < v → v ≤ y1 →
    ∀ i threshold sign, |sign| = 1 →
    Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel
      (fun y => horizontalJet (f i) a (x,y)) b u v threshold sign)) ∧
    Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel
      (fun y => horizontalJet (f i) a (x,y)) b u v threshold sign)) ≤ K

def horizontalGoodCounts {ι : Type*} (f : ι → ℝ × ℝ → ℝ)
    (N K : ℕ) (x0 x1 y0 y1 : ℝ) : Prop :=
  ∀ B : ι → ℝ, ∀ C x : ℝ, x ∈ Ioo x0 x1 →
    Finite (ConnectedComponents (Prod.mk x ⁻¹' horizontalGood f B N C x0 x1 y0 y1)) ∧
    Nat.card (ConnectedComponents (Prod.mk x ⁻¹' horizontalGood f B N C x0 x1 y0 y1)) ≤ K

/-- Actual mixed derivative superlevels in the horizontal good set. -/
def mixedBad {ι : Type*} (f : ι → ℝ × ℝ → ℝ) (B : ι → ℝ)
    (N a : ℕ) (C Lx Ly : ℝ) (H : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | p ∈ H ∧ ∃ i, ∃ b ≤ N-a,
    C*B i/(Lx^a*Ly^b) < |mixedJet (f i) a b p|}

theorem isOpen_mixedBad {ι : Type*} [Fintype ι]
    {f : ι → ℝ × ℝ → ℝ} {B : ι → ℝ} {N a : ℕ} {C Lx Ly : ℝ}
    {R H : Set (ℝ × ℝ)} (hR : IsOpen R) (hH : IsOpen H) (hsub : H ⊆ R)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) R) : IsOpen (mixedBad f B N a C Lx Ly H) := by
  have he : mixedBad f B N a C Lx Ly H = ⋃ i, ⋃ b : ℕ, ⋃ (_ : b ≤ N-a),
      H ∩ {p | C*B i/(Lx^a*Ly^b) < |mixedJet (f i) a b p|} := by
    ext p
    simp only [mixedBad, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    aesop
  rw [he]
  apply isOpen_iUnion
  intro i
  apply isOpen_iUnion
  intro b
  apply isOpen_iUnion
  intro _
  exact (((continuousOn_mixedJet hR (hf i) a b).mono hsub).abs.isOpen_inter_preimage hH isOpen_Ioi)

theorem horizontalGood_amplitude {ι : Type*} {f : ι → ℝ × ℝ → ℝ}
    {B : ι → ℝ} {N : ℕ} {C x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hC : 1 ≤ C) (hB : ∀ i, 0 ≤ B i)
    (hamp : ∀ i p, p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1 → |f i p| ≤ B i)
    {p : ℝ × ℝ} (hp : p ∈ horizontalGood f B N C x0 x1 y0 y1)
    (i : ι) (a : ℕ) (ha : a ≤ N) :
    |horizontalJet (f i) a p| ≤ C*B i/(x1-x0)^a := by
  by_cases haz : a = 0
  · subst a
    simp only [horizontalJet_zero, pow_zero, div_one]
    exact (hamp i p hp.1).trans (by nlinarith [hB i])
  by_cases hBi : B i = 0
  · have hz := mixedJet_eq_zero_of_amplitude_zero
      (f := f i) (fun p hp => by simpa only [hBi] using hamp i p hp) a 0 hp.1
    change horizontalJet (f i) a p = 0 at hz
    simp only [hz, hBi, mul_zero, zero_div, abs_zero, le_refl]
  exact (hp.2 i ⟨a,Nat.lt_succ_iff.mpr ha⟩ (Nat.pos_of_ne_zero haz)
    (lt_of_le_of_ne (hB i) (Ne.symm hBi))).le

/-- Rectangle preparation from the three actual component bounds. The bounds
are discharged from fixed positive-jet graph format in PreparationFormat. -/
theorem rectangle_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ι → ℝ × ℝ → ℝ) (B : ι → ℝ)
      (x0 x1 y0 y1 : ℝ), x0 < x1 → y0 < y1 → (∀ i, 0 ≤ B i) →
      (∀ i, ContDiffOn ℝ ∞ (f i) (Ioo x0 x1 ×ˢ Ioo y0 y1)) →
      (∀ i p, p ∈ Ioo x0 x1 ×ˢ Ioo y0 y1 → |f i p| ≤ B i) →
      horizontalCounts f N K x0 x1 y0 y1 →
      verticalCounts f N K x0 x1 y0 y1 →
      horizontalGoodCounts f N K x0 x1 y0 y1 →
      ∃ G : Set (ℝ × ℝ), MeasurableSet G ∧ G ⊆ Ioo x0 x1 ×ˢ Ioo y0 y1 ∧
        volume ((Ioo x0 x1 ×ˢ Ioo y0 y1) \ G) ≤ ENNReal.ofReal (ε*(x1-x0)*(y1-y0)) ∧
        ∀ p ∈ G, ∀ i a b, a+b ≤ N →
          |mixedJet (f i) a b p| ≤ C*B i/((x1-x0)^a*(y1-y0)^b) := by
  classical
  obtain ⟨Ch,hCh,hhor⟩ := horizontalGood_volume hDD (ι := ι) N K (ε/2) (by positivity)
  let δ : ℝ := ε/(2*((N:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hex : ∀ a : Fin (N+1), ∃ D : ℝ, 1 ≤ D ∧ ∀ (g : ι → ℝ → ℝ) (A : ι → ℝ)
      (l r : ℝ) (U : Set ℝ), l < r → IsOpen U → U ⊆ Ioo l r →
      Finite (ConnectedComponents U) → Nat.card (ConnectedComponents U) ≤ K →
      (∀ i,0 ≤ A i) → (∀ i,ContDiffOn ℝ (↑(N-a.val) : WithTop ℕ∞) (g i) U) →
      (∀ i y, y ∈ U → |g i y| ≤ A i) →
      (∀ u v,l ≤ u → u < v → v ≤ r → Ioo u v ⊆ U →
        ∀ i n,0<n → n ≤ N-a.val → ∀ t z,|z|=1 →
          Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel (g i) n u v t z)) ∧
          Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel (g i) n u v t z)) ≤ K) →
      volume {y | y∈U ∧ ∃ i,∃n≤N-a.val,D*A i/(r-l)^n < |iteratedDeriv n (g i) y|}
        ≤ ENNReal.ofReal (δ*(r-l)) :=
    fun a => open_component_preparation hDD (N-a.val) K K δ hδ
  choose D hD hprep using hex
  let C : ℝ := Ch*(1+∑a,D a)
  have hD0 : ∀ a,0 ≤ D a := fun a => zero_le_one.trans (hD a)
  have hsum : 0 ≤ ∑a,D a := Finset.sum_nonneg (fun a _ => hD0 a)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le hCh (by linarith)
  have hDC : ∀ a, D a*Ch ≤ C := by
    intro a
    have ht := Finset.single_le_sum (fun b _ => hD0 b) (Finset.mem_univ a)
    dsimp [C]
    nlinarith [zero_le_one.trans hCh]
  refine ⟨C,hC,?_⟩
  intro f B x0 x1 y0 y1 hx hy hB hf hamp hX hY hHcount
  let R := Ioo x0 x1 ×ˢ Ioo y0 y1
  let H := horizontalGood f B N Ch x0 x1 y0 y1
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hHo : IsOpen H := isOpen_horizontalGood hf
  have hHR : H ⊆ R := fun _ hp => hp.1
  have hLx : 0 < x1-x0 := sub_pos.mpr hx
  have hLy : 0 < y1-y0 := sub_pos.mpr hy
  have hHbad := hhor f B x0 x1 y0 y1 hx hy hB hf hamp hX
  let E : Fin (N+1) → Set (ℝ × ℝ) := fun a => mixedBad f B N a.val C (x1-x0) (y1-y0) H
  have hEm : ∀ a, MeasurableSet (E a) := fun a =>
    (isOpen_mixedBad hR hHo hHR hf).measurableSet
  have hEa : ∀ a, volume (E a) ≤ ENNReal.ofReal (δ*(x1-x0)*(y1-y0)) := by
    intro a
    have hb := rectangle_section_budget (E := E a) (hEm a)
      (fun p hp => ⟨(hHR hp.1).1,mem_univ _⟩) (a := x0) (b := x1) (q := δ*(y1-y0)) ?_
    · apply hb.trans_eq
      rw [← ENNReal.ofReal_mul (mul_nonneg hδ.le hLy.le)]
      congr 1
      ring
    intro x hx'
    let U := Prod.mk x ⁻¹' H
    have hUo : IsOpen U := hHo.preimage (continuous_const.prodMk continuous_id)
    have hUs : U ⊆ Ioo y0 y1 := fun _ hu => (hHR hu).2
    have hUc := hHcount B Ch x hx'
    have hbound := hprep a (fun i y => horizontalJet (f i) a.val (x,y))
      (fun i => Ch*B i/(x1-x0)^a.val) y0 y1 U hy hUo hUs hUc.1 hUc.2
      (fun i => div_nonneg (mul_nonneg (zero_le_one.trans hCh) (hB i)) (pow_nonneg hLx.le _))
      (fun i => ((contDiffOn_sectionY
        (contDiffOn_horizontalJet hR (hf i) a.val) hx').mono hUs).of_le
        (WithTop.coe_le_coe.mpr (show ((N-a.val) : ℕ∞) ≤ ⊤ from le_top)))
      (fun i y hy' => horizontalGood_amplitude hx hCh hB hamp hy' i a.val
        (Nat.lt_succ_iff.mp a.isLt))
      (fun u v hu huv hv _ i n hn hnN t z hz => hY x hx' a.val n hn
        (by omega) u v hu huv hv i t z hz)
    apply (measure_mono ?_).trans hbound
    intro y hyE
    obtain ⟨hyH,i,b,hb,hbad⟩ := hyE
    refine ⟨hyH,i,b,hb,?_⟩
    have hcoef : D a * (Ch*B i/(x1-x0)^a.val)/(y1-y0)^b ≤
        C*B i/((x1-x0)^a.val*(y1-y0)^b) := by
      calc
        _ = (D a*Ch)*B i/((x1-x0)^a.val*(y1-y0)^b) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hDC a) (hB i)) (by positivity)
    rw [mixedJet_eq_iteratedDeriv] at hbad
    exact hcoef.trans_lt hbad
  obtain ⟨G,hGm,hGH,hGbad,hGood⟩ := preparation_common_measurable_good_set
    volume H hHo.measurableSet Finset.univ E (fun a _ => hEm a)
    (fun a p => ∀ i b, b ≤ N-a.val →
      |mixedJet (f i) a.val b p| ≤ C*B i/((x1-x0)^a.val*(y1-y0)^b))
    (fun _ => δ*(x1-x0)*(y1-y0)) (fun _ _ => by positivity)
    (fun a _ => hEa a) (fun a _ p hp hn i b hb =>
      le_of_not_gt (fun hbad => hn ⟨hp,i,b,hb,hbad⟩))
  have hsumBudget : (∑_a : Fin (N+1),δ*(x1-x0)*(y1-y0)) =
      (ε/2)*(x1-x0)*(y1-y0) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    dsimp [δ]
    field_simp
    <;> ring
  refine ⟨G,hGm,hGH.trans hHR,?_,?_⟩
  · have hsub : R \ G ⊆ (R \ H) ∪ (H \ G) := by
      intro p hp
      by_cases hh : p∈H
      · exact Or.inr ⟨hh,hp.2⟩
      · exact Or.inl ⟨hp.1,hh⟩
    calc
      _ ≤ volume (R \ H) + volume (H \ G) := (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal ((ε/2)*(x1-x0)*(y1-y0)) +
          ENNReal.ofReal ((ε/2)*(x1-x0)*(y1-y0)) := by
        apply add_le_add hHbad
        simpa only [hsumBudget] using hGbad
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro p hp i a b hab
    have ha : a < N+1 := by omega
    have hb : b ≤ N-a := by omega
    exact hGood p hp ⟨a,ha⟩ (Finset.mem_univ _) i b hb

end PaperI.Preparation
