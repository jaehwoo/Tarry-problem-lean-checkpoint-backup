import PaperILean.SectionIntervalTransport

/-! I3230 and I3244[141,217): the full unit-interval count of original indexed
labels. The finite cut list and actual component sections are constructed
internally. Repeated representatives retain their original multiplicities. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm
namespace PaperI.RegularUnitIntervalPacking
open Set Classical ActualDSections ExceptionalDSections ExceptionalFiberPackingStage
open RegularSectionDifferential RegularSectionRates

private theorem indexed_cover_card_bound {ι κ : Type*}
    (J : Finset ι) (Q : Finset κ) (p : κ → ι → Prop) (B : ℝ)
    (hcover : ∀ i ∈ J, ∃ c ∈ Q, p c i)
    (hbound : ∀ c ∈ Q, ((J.filter (p c)).card : ℝ) ≤ B) :
    (J.card : ℝ) ≤ (Q.card : ℝ) * B := by
  classical
  have hsub : J ⊆ Q.biUnion (fun c => J.filter (p c)) := by
    intro i hi
    obtain ⟨c,hc,hci⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hi,hci⟩⟩
  calc
    (J.card : ℝ) ≤ ((Q.biUnion (fun c => J.filter (p c))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ((∑ c ∈ Q, (J.filter (p c)).card) : ℕ) :=
      Nat.cast_le.mpr Finset.card_biUnion_le
    _ = ∑ c ∈ Q, ((J.filter (p c)).card : ℝ) := by norm_cast
    _ ≤ ∑ _c ∈ Q, B := Finset.sum_le_sum hbound
    _ = (Q.card : ℝ) * B := by simp

private theorem section_label_count {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (N s d : ℕ)
    (hF : F.Bounded N s d) : Fintype.card (SectionLabel F) ≤ N * N := by
  classical
  calc
    Fintype.card (SectionLabel F) = ∑ i : Fin F.n, F.m i := by
      simp [SectionLabel, Fintype.card_sigma]
    _ ≤ ∑ _i : Fin F.n, N := Finset.sum_le_sum (fun i _ => hF.sections_le i)
    _ = F.n * N := by simp
    _ ≤ N * N := Nat.mul_le_mul_right N hF.pieces_le

private theorem nat_le_power (P : ℝ) (hP : 2 ≤ P) (n : ℕ) :
    (n : ℝ) ≤ P ^ (n : ℝ) := by
  have hp : 0 < P := by linarith
  have h : (n : ℝ) + 1 ≤ P ^ (n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, Real.rpow_add hp, Real.rpow_one]
      have hm := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hp.le (n : ℝ))
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  linarith

private theorem two_power_bounds (P Λ q e₁ e₂ : ℝ) (n₁ n₂ : ℕ)
    (hP : 2 ≤ P) (hΛ : 0 ≤ Λ) (hq : 0 ≤ q)
    (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) :
    (n₁ : ℝ) * (Λ * (P ^ e₁) ^ q) + Λ * P ^ ((n₂ : ℝ) + q * e₂) ≤
      Λ * P ^ (1 + (n₁ : ℝ) + (n₂ : ℝ) + q * (e₁ + e₂)) := by
  have hp : 0 < P := by linarith
  have hp1 : 1 ≤ P := by linarith
  have hn₁ : 0 ≤ (n₁ : ℝ) := Nat.cast_nonneg _
  have hn₂ : 0 ≤ (n₂ : ℝ) := Nat.cast_nonneg _
  have hq₁ := mul_nonneg hq he₁
  have hq₂ := mul_nonneg hq he₂
  let z : ℝ := (n₁ : ℝ) + (n₂ : ℝ) + q * (e₁ + e₂)
  have hfirst : (n₁ : ℝ) * (Λ * (P ^ e₁) ^ q) ≤ Λ * P ^ z := by
    calc
      (n₁ : ℝ) * (Λ * (P ^ e₁) ^ q) ≤ P ^ (n₁ : ℝ) * (Λ * (P ^ e₁) ^ q) :=
        mul_le_mul_of_nonneg_right (nat_le_power P hP n₁) (by positivity)
      _ = Λ * P ^ ((n₁ : ℝ) + e₁ * q) := by
        rw [← Real.rpow_mul hp.le, ← mul_assoc, mul_comm _ Λ, mul_assoc,
          ← Real.rpow_add hp]
      _ ≤ Λ * P ^ z := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (by dsimp [z]; nlinarith)) hΛ
  have hsecond : Λ * P ^ ((n₂ : ℝ) + q * e₂) ≤ Λ * P ^ z :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hp1 (by dsimp [z]; nlinarith)) hΛ
  calc
    (n₁ : ℝ) * (Λ * (P ^ e₁) ^ q) + Λ * P ^ ((n₂ : ℝ) + q * e₂) ≤
        2 * (Λ * P ^ z) := by linarith
    _ ≤ P * (Λ * P ^ z) := mul_le_mul_of_nonneg_right hP (by positivity)
    _ = Λ * (P ^ (1 : ℝ) * P ^ z) := by rw [Real.rpow_one]; ring
    _ = Λ * P ^ (1 + (n₁ : ℝ) + (n₂ : ℝ) + q * (e₁ + e₂)) := by
      rw [← Real.rpow_add hp]
      congr 2
      dsimp [z]
      ring

private theorem packing_on_subset {ι : Type} (J J' : Finset ι)
    (g : ι → Fin 6 → ℝ) (Λ q : ℝ) (hsub : J' ⊆ J)
    (hpack : ∀ i ∈ J, ∀ R : ℝ, 2 ≤ R →
      ((J.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
        Λ * R ^ q) :
    ∀ i ∈ J', ∀ R : ℝ, 2 ≤ R →
      ((J'.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
        Λ * R ^ q := by
  classical
  intro i hi R hR
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hpack i (hsub hi) R hR)
  intro j hj
  obtain ⟨hjJ,hjR⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hsub hjJ,hjR⟩

private theorem regular_labels_card_bound {E : Set (Fin 6 → ℝ)}
    (F : ComponentSectionAtlas (actualDRelation E)) (C : Finset ℝ)
    (N s d K : ℕ) (hF : F.Bounded N s d) (hPowers : C.powerset.card ≤ 2 ^ K)
    (hCover : ∀ t : ℝ, t ∈ C ∨ ∃ L ∈ C.powerset, t ∈ axisCutCell C L)
    (P Λ q e a b : ℝ) (hΛ : 0 ≤ Λ) (hR : 2 ≤ P ^ e) (hab : b - a ≤ 1)
    (hPair : ∀ L ∈ C.powerset, ∀ r : SectionLabel F, ∀ x y : Fin 6 → ℝ,
      x ∈ actualDRegion F r → y ∈ actualDRegion F r →
      x 3 ∈ axisCutCell C L → y 3 ∈ axisCutCell C L → |y 3 - x 3| ≤ 1 →
      relativeNeighborhoodRadius x y ≤ P ^ e)
    {ι : Type} (J : Finset ι) (g : ι → Fin 6 → ℝ)
    (hg : ∀ i ∈ J, g i ∈ E) (hd : ∀ i ∈ J, g i 3 ∉ C)
    (hi : ∀ i ∈ J, g i 3 ∈ Icc a b)
    (hpack : ∀ i ∈ J, ∀ R : ℝ, 2 ≤ R →
      ((J.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
        Λ * R ^ q) :
    (J.card : ℝ) ≤ ((2 ^ K * N * N : ℕ) : ℝ) * (Λ * (P ^ e) ^ q) := by
  classical
  let Q := C.powerset.product (Finset.univ : Finset (SectionLabel F))
  let eligible : (Finset ℝ × SectionLabel F) → ι → Prop :=
    fun c i => g i 3 ∈ axisCutCell C c.1 ∧ g i ∈ actualDRegion F c.2
  have hB : 0 ≤ Λ * (P ^ e) ^ q := mul_nonneg hΛ (Real.rpow_nonneg (by linarith) _)
  have hcount : (J.card : ℝ) ≤ (Q.card : ℝ) * (Λ * (P ^ e) ^ q) := by
    apply indexed_cover_card_bound J Q eligible
    · intro i hiJ
      obtain ⟨L,hL,hit⟩ := (hCover (g i 3)).resolve_left (hd i hiJ)
      obtain ⟨r,hir⟩ := actual_d_region_cover F (g i) (hg i hiJ)
      exact ⟨(L,r),Finset.mem_product.mpr ⟨hL,Finset.mem_univ r⟩,hit,hir⟩
    · intro c hc
      letI : DecidablePred (eligible c) := fun i => Classical.propDecidable (eligible c i)
      change ((J.filter (eligible c)).card : ℝ) ≤ Λ * (P ^ e) ^ q
      by_cases hn : (J.filter (eligible c)).Nonempty
      · obtain ⟨i,hiJc⟩ := hn
        obtain ⟨hiJ,hic⟩ := Finset.mem_filter.mp hiJc
        apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hpack i hiJ (P ^ e) hR)
        intro j hj
        have hj' : j ∈ J ∧ eligible c j := by simpa only [Finset.mem_filter] using hj
        obtain ⟨hjJ,hjc⟩ := hj'
        refine Finset.mem_filter.mpr ⟨hjJ,?_⟩
        have hiI := hi i hiJ
        have hjI := hi j hjJ
        exact hPair c.1 (Finset.mem_product.mp hc).1 c.2 (g i) (g j)
          hic.2 hjc.2 hic.1 hjc.1
          (abs_le.mpr ⟨by linarith [hiI.1,hiI.2,hjI.1,hjI.2],
            by linarith [hiI.1,hiI.2,hjI.1,hjI.2]⟩)
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,Finset.card_empty,Nat.cast_zero] using hB
  have hQ : Q.card ≤ 2 ^ K * N * N := by
    dsimp [Q]
    rw [Finset.card_product,Finset.card_univ]
    calc
      C.powerset.card * Fintype.card (SectionLabel F) ≤ 2 ^ K * (N * N) :=
        Nat.mul_le_mul hPowers (section_label_count F N s d hF)
      _ = 2 ^ K * N * N := by ring
  exact hcount.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hQ) hB)

private theorem exponent_budget (m MF NS ME n₁ n₂ : ℕ) (S W q : ℝ)
    (hS : 0 ≤ S) (hW : 0 ≤ W) (hq : 0 ≤ q) :
    1 + (n₁ : ℝ) + (n₂ : ℝ) + q *
      ((2 * ((MF : ℝ) * (6 * (m : ℝ) + 3 * S + 3 * W + 4) + 5) +
        9 * ((NS : ℝ) + S + 2 * W + 1) + 15) +
        ((ME : ℝ) * (6 * (m : ℝ) + 3 * S + 3 * W + 4) + 5)) ≤
      ((n₁ + n₂ + 1 + ((2 * MF + ME) * (6 * m + 10) + 9 * NS + 66) : ℕ) : ℝ) *
        (1 + q) * (1 + S + W) := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hMF : 0 ≤ (MF : ℝ) := Nat.cast_nonneg _
  have hNS : 0 ≤ (NS : ℝ) := Nat.cast_nonneg _
  have hME : 0 ≤ (ME : ℝ) := Nat.cast_nonneg _
  have hn₁ : 0 ≤ (n₁ : ℝ) := Nat.cast_nonneg _
  have hn₂ : 0 ≤ (n₂ : ℝ) := Nat.cast_nonneg _
  let w : ℝ := 1 + S + W
  let c : ℝ := (2 * (MF : ℝ) + ME) * (6 * (m : ℝ) + 10) + 9 * NS + 66
  let d : ℝ := (n₁ : ℝ) + n₂ + 1
  have hw : 1 ≤ w := by dsimp [w]; linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hbase : 6 * (m : ℝ) + 3 * S + 3 * W + 4 ≤ (6 * (m : ℝ) + 10) * w := by
    dsimp [w]
    nlinarith [mul_nonneg hm hS,mul_nonneg hm hW]
  have hleft := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2 * (MF : ℝ) + ME)
  have hright : 9 * (NS : ℝ) + 9 * S + 18 * W + 39 ≤ (9 * (NS : ℝ) + 66) * w := by
    dsimp [w]
    nlinarith [mul_nonneg hNS hS,mul_nonneg hNS hW]
  have hexp :
      (2 * ((MF : ℝ) * (6 * (m : ℝ) + 3 * S + 3 * W + 4) + 5) +
        9 * ((NS : ℝ) + S + 2 * W + 1) + 15) +
        ((ME : ℝ) * (6 * (m : ℝ) + 3 * S + 3 * W + 4) + 5) ≤ c * w := by
    dsimp [c]
    nlinarith only [hleft,hright]
  have hqexp := mul_le_mul_of_nonneg_left hexp hq
  have hdw : d ≤ d * w := by nlinarith
  have hcw : 0 ≤ c * w := mul_nonneg hc (by linarith)
  have hqdw : 0 ≤ q * d * w := mul_nonneg (mul_nonneg hq hd) (by linarith)
  push_cast
  dsimp only [d,c,w] at hqexp hdw hcw hqdw
  nlinarith only [hqexp,hdw,hcw,hqdw]

/-- I3230, including intervals that meet or cross the actual exceptional list.
The bound counts every original label in the interval, so it also bounds the
labels of the saved fixed-order assignment. The sole counting premise is the
indexed relative-neighborhood packing hypothesis at I1338. All atlas, section,
path and exceptional-fiber comparisons are derived from the retained published
inputs. The uniform exponent is chosen before coefficients, windows and labels. -/
theorem regular_d_sections_assertion_ii
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) (hk : 2 ≤ k) :
    ∃ B : ℕ, ∀ (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∀ (P Cs Cw Λ q : ℝ) (S0 : AugmentedState k) (a b : ℝ),
      2 ≤ P → 0 ≤ Λ → 0 ≤ q → b - a ≤ 1 →
      (∀ g ∈ E, augmentedStateNorm (augmentedPullback S0 g) ≤ P ^ Cw) →
      (∀ g ∈ E, P ^ (-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 g)) (Fin.last 4)) →
      ∀ {ι : Type} (J : Finset ι) (g : ι → Fin 6 → ℝ),
      (∀ i ∈ J, g i ∈ E) → (∀ i ∈ J, g i 3 ∈ Icc a b) →
      (∀ i ∈ J, ∀ R : ℝ, 2 ≤ R →
        ((J.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ R)).card : ℝ) ≤
          Λ * R ^ q) →
      (J.card : ℝ) ≤ Λ * P ^ ((B : ℝ) * (1 + q) * (1 + max Cs 0 + max Cw 0)) := by
  classical
  obtain ⟨N,sOut,dOut,K,hCuts⟩ := actual_d_exceptional_list hCell hHardt hQE s D
  obtain ⟨MF,NS,hRadius⟩ := SectionIntervalTransport.actual_section_class_radius
    hCell hPath hHardt hQE hNash hPiece k s D (sOut + K) (max dOut 1) hk
  obtain ⟨NF,ME,hException⟩ := exceptional_levels_card_bound
    hCell hPath hHardt hQE hNash hPiece k s D hk
  let m := Fintype.card (AugmentedCoordinateIndex k)
  let nReg := 2 ^ K * N * N
  let nExc := K * NF
  let budget := (2 * MF + ME) * (6 * m + 10) + 9 * NS + 66
  refine ⟨nReg + nExc + 1 + budget,?_⟩
  intro A E hAc hAd hAE P Cs Cw Λ q S0 a b hP hΛ hq hab hwindow hpivot ι J g hg hi hpack
  obtain ⟨F,C,hF,_hAssign,hC,hPowers,hCover,_hDisjoint,hCells⟩ := hCuts A E hAc hAd hAE
  let ePair : ℝ := 2 * ((MF : ℝ) * (6 * (m : ℝ) + 3 * max Cs 0 + 3 * max Cw 0 + 4) + 5) +
    (9 * ((NS : ℝ) + max Cs 0 + 2 * max Cw 0 + 1) + 15)
  let eExc : ℝ := (ME : ℝ) * (6 * (m : ℝ) + 3 * max Cs 0 + 3 * max Cw 0 + 4) + 5
  have hPair : ∀ L ∈ C.powerset, ∀ r : SectionLabel F, ∀ x y : Fin 6 → ℝ,
      x ∈ actualDRegion F r → y ∈ actualDRegion F r →
      x 3 ∈ axisCutCell C L → y 3 ∈ axisCutCell C L → |y 3 - x 3| ≤ 1 →
      relativeNeighborhoodRadius x y ≤ P ^ ePair := by
    intro L hL r x y hxr hyr hxc hyc hxy
    rcases (hCells L hL).2.2.2 with hempty | ⟨i,hU,hSections,_hSectionMem,_hBijection⟩
    · have hxf : x ∈ projectionFiber (actualDRelation E) (fun _ => x 3) :=
        ⟨actual_d_region_subset F r hxr,rfl⟩
      rw [hempty (x 3) hxc] at hxf
      exact False.elim hxf
    · rcases r with ⟨ri,rj⟩
      obtain ⟨hri,_hxFiber,_hxComponent⟩ :=
        (componentSectionRegion_mem_iff (actualDRelation E) (F.piece ri) (F.sectionFn ri rj)
          (F.section_mem ri rj) (fun _ => x 3) x).mp hxr
      have hriEq : ri = i := by
        by_contra hne
        exact Set.disjoint_left.mp (F.disjoint hne) hri (hU hxc)
      subst ri
      exact hRadius P Cs Cw S0 A E hP hAc hAd hAE hwindow hpivot F C L i rj hU
        (hSections rj).2.1 x y hxr hyr hxc hyc hxy
  have hePair : 1 ≤ ePair := by
    have h₁ : 0 ≤ (MF : ℝ) * (6 * (m : ℝ) + 3 * max Cs 0 + 3 * max Cw 0 + 4) := by
      positivity
    have h₂ : 0 ≤ 9 * ((NS : ℝ) + max Cs 0 + 2 * max Cw 0 + 1) := by positivity
    dsimp only [ePair]
    linarith
  have heExc : 0 ≤ eExc := by dsimp only [eExc]; positivity
  have hpos : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hR : 2 ≤ P ^ ePair := hP.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP1 hePair)
  let Jreg := J.filter (fun i => g i 3 ∉ C)
  let Jexc := J.filter (fun i => g i 3 ∈ C)
  have hreg : (Jreg.card : ℝ) ≤ (nReg : ℝ) * (Λ * (P ^ ePair) ^ q) := by
    apply regular_labels_card_bound F C N sOut dOut K hF hPowers hCover
      P Λ q ePair a b hΛ hR hab hPair Jreg g
    · intro i hii
      exact hg i (Finset.mem_filter.mp hii).1
    · intro i hii
      exact (Finset.mem_filter.mp hii).2
    · intro i hii
      exact hi i (Finset.mem_filter.mp hii).1
    · exact packing_on_subset J Jreg g Λ q (Finset.filter_subset _ _) hpack
  have hexc : (Jexc.card : ℝ) ≤ Λ * P ^ ((nExc : ℝ) + q * eExc) := by
    apply hException P Cs Cw Λ q S0 A E C K hP hΛ hq hAc hAd hAE hC hwindow hpivot Jexc g
    · intro i hii
      exact hg i (Finset.mem_filter.mp hii).1
    · intro i hii
      exact (Finset.mem_filter.mp hii).2
    · exact packing_on_subset J Jexc g Λ q (Finset.filter_subset _ _) hpack
  have hcard : (J.card : ℝ) = (Jreg.card : ℝ) + (Jexc.card : ℝ) := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := J) (fun i => g i 3 ∈ C)
    dsimp only [Jreg,Jexc]
    exact_mod_cast h.symm.trans (Nat.add_comm _ _)
  have hExp : 1 + (nReg : ℝ) + (nExc : ℝ) + q * (ePair + eExc) ≤
      ((nReg + nExc + 1 + budget : ℕ) : ℝ) * (1 + q) * (1 + max Cs 0 + max Cw 0) := by
    simpa only [ePair,eExc,budget,add_assoc] using
      exponent_budget m MF NS ME nReg nExc (max Cs 0) (max Cw 0) q
        (le_max_right _ _) (le_max_right _ _) hq
  calc
    (J.card : ℝ) = (Jreg.card : ℝ) + (Jexc.card : ℝ) := hcard
    _ ≤ (nReg : ℝ) * (Λ * (P ^ ePair) ^ q) + Λ * P ^ ((nExc : ℝ) + q * eExc) :=
      add_le_add hreg hexc
    _ ≤ Λ * P ^ (1 + (nReg : ℝ) + (nExc : ℝ) + q * (ePair + eExc)) :=
      two_power_bounds P Λ q ePair eExc nReg nExc hP hΛ hq (by linarith) heExc
    _ ≤ Λ * P ^ (((nReg + nExc + 1 + budget : ℕ) : ℝ) * (1 + q) *
        (1 + max Cs 0 + max Cw 0)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 hExp) hΛ

end PaperI.RegularUnitIntervalPacking
