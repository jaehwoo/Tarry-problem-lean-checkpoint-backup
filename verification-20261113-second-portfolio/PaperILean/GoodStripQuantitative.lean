import PaperILean.GoodStripSectionPreparation
import PaperILean.PreparationRectangle
import PaperILean.PreparationFormat

open scoped BigOperators

noncomputable section

namespace PaperI.GoodStrips

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

abbrev Rect (x0 x1 y0 y1 : ℝ) : Set (ℝ × ℝ) := Ioo x0 x1 ×ˢ Ioo y0 y1

abbrev horizontalSection (U : Set (ℝ × ℝ)) (y : ℝ) : Set ℝ := (fun x => (x,y)) ⁻¹' U
abbrev verticalSection (U : Set (ℝ × ℝ)) (x : ℝ) : Set ℝ := Prod.mk x ⁻¹' U

abbrev Jet (f : ℝ × ℝ → ℝ) (a b : ℕ) : ℝ × ℝ → ℝ := Preparation.mixedJet f a b

def horizontalGoodOn {ι : Type} (U : Set (ℝ × ℝ)) (f : ι → ℝ × ℝ → ℝ)
    (N : ℕ) (A : ι → ℝ) (C L : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ U ∧ ∀ i (n : Fin (N+1)), 0 < A i →
    |Jet (f i) n.val 0 p| < C*A i/L^n.val}

def verticalBadOn {ι : Type} (V : Set (ℝ × ℝ)) (f : ι → ℝ × ℝ → ℝ)
    (N a : ℕ) (A : ι → ℝ) (C L W : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ V ∧ ∃ i, ∃ n ≤ N-a, C*A i/(L^a*W^n) < |Jet (f i) a n p|}

theorem horizontalGoodOn_section_open {ι : Type} [Fintype ι] (U : Set (ℝ × ℝ))
    (f : ι → ℝ × ℝ → ℝ) (N : ℕ) (A : ι → ℝ) (C L x : ℝ)
    (hU : IsOpen (verticalSection U x))
    (hc : ∀ i n, n ≤ N → ContinuousOn (fun y => Jet (f i) n 0 (x,y))
      (verticalSection U x)) :
    IsOpen (verticalSection (horizontalGoodOn U f N A C L) x) := by
  classical
  have he : verticalSection (horizontalGoodOn U f N A C L) x =
      verticalSection U x ∩ ⋂ i, ⋂ n : Fin (N+1), if 0 < A i then
        verticalSection U x ∩ {y | |Jet (f i) n.val 0 (x,y)| < C*A i/L^n.val} else univ := by
    ext y
    simp only [horizontalGoodOn, mem_preimage, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hy,h⟩
      refine ⟨hy,fun i n => ?_⟩
      split_ifs with hi
      · exact ⟨hy,h i n hi⟩
      · exact mem_univ _
    · rintro ⟨hy,h⟩
      refine ⟨hy,fun i n hi => ?_⟩
      have hn := h i n
      rw [if_pos hi] at hn
      exact hn.2
  rw [he]
  apply hU.inter
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro n
  split_ifs with h
  · exact ((hc i n.val (Nat.lt_succ_iff.mp n.isLt)).abs.isOpen_inter_preimage hU isOpen_Iio)
  · exact isOpen_univ

private theorem horizontalGoodOn_bound {ι : Type} {U : Set (ℝ × ℝ)}
    {f : ι → ℝ × ℝ → ℝ} {N : ℕ} {A : ι → ℝ} {C L : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hz : ∀ i p, p ∈ U → A i = 0 → ∀ n ≤ N, Jet (f i) n 0 p = 0)
    {p : ℝ × ℝ} (hp : p ∈ horizontalGoodOn U f N A C L) (i : ι) (n : ℕ) (hn : n ≤ N) :
    |Jet (f i) n 0 p| ≤ C*A i/L^n := by
  rcases (hA i).eq_or_lt with he | hi
  · rw [hz i p hp.1 he.symm n hn, ← he]
    simp
  · exact (hp.2 i ⟨n,by omega⟩ hi).le

private theorem horizontal_zero_of_open {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hU : IsOpen U) (hzero : ∀ p ∈ U, f p = 0) (p : ℝ × ℝ) (hp : p ∈ U) (n : ℕ) :
    Jet f n 0 p = 0 := by
  rcases p with ⟨x,y⟩
  have hc : Continuous (fun z : ℝ => (z,y)) := continuous_id.prodMk continuous_const
  have hn : ∀ᶠ z in nhds x, (z,y) ∈ U := hc.continuousAt (hU.mem_nhds hp)
  have he : (fun z : ℝ => f (z,y)) =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hn] with z hz
    exact hzero _ hz
  change Preparation.mixedJet f n 0 (x,y) = 0
  rw [Preparation.mixedJet_zero_right,Preparation.horizontalJet_eq_iteratedDeriv,he.iteratedDeriv_eq]
  cases n <;> simp [iteratedDeriv_eq_iteratedFDeriv]

/-- Two nested, actual section preparations. Every discarded set is a literal
derivative set. The interval witnesses stay local to the section estimate. -/
theorem quantitative_preparation_on_open_subsets
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type} [Fintype ι] (N KU KD KV : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧
    ∀ (η : ℝ), 0 < η → η ≤ 1 →
    ∀ (f : ι → ℝ × ℝ → ℝ) (A : ι → ℝ) (x0 x1 y0 y1 : ℝ)
      (U : Set (ℝ × ℝ)),
      x0 < x1 → y0 < y1 → IsOpen U → U ⊆ Rect x0 x1 y0 y1 →
      (∀ i, 0 ≤ A i) → (∀ i p, p ∈ U → |f i p| ≤ A i) →
      (∀ i y, ContDiffOn ℝ N (fun x => f i (x,y)) (horizontalSection U y)) →
      (∀ i a, a ≤ N → ∀ x, ContDiffOn ℝ ((N-a : ℕ) : WithTop ℕ∞)
        (fun y => Jet (f i) a 0 (x,y)) (verticalSection U x)) →
      (∀ y, Preparation.ComponentBound KU (horizontalSection U y)) →
      (∀ C x, Preparation.ComponentBound KV
        (verticalSection (horizontalGoodOn U f N A C (x1-x0)) x)) →
      (∀ C, MeasurableSet (horizontalGoodOn U f N A C (x1-x0))) →
      (∀ C₀ C a, MeasurableSet (verticalBadOn (horizontalGoodOn U f N A C₀ (x1-x0)) f N a A C (x1-x0) (y1-y0))) →
      (∀ i n, 0 < n → n ≤ N → ∀ y l r T sign,
        Ioo l r ⊆ horizontalSection U y →
        Preparation.ComponentBound KD (signedIteratedDerivativeSuperlevel (fun x => f i (x,y)) n l r T sign)) →
      (∀ i a b, 0 < b → a+b ≤ N → ∀ x l r T sign,
        Ioo l r ⊆ verticalSection U x →
        Preparation.ComponentBound KD (signedIteratedDerivativeSuperlevel
          (fun y => Jet (f i) a 0 (x,y)) b l r T sign)) →
      ∃ G : Set (ℝ × ℝ), MeasurableSet G ∧ G ⊆ U ∧
        volume (U \ G) ≤ ENNReal.ofReal (η*(x1-x0)*(y1-y0)) ∧
        ∀ p ∈ G, ∀ i a b, a+b ≤ N →
          |Jet (f i) a b p| ≤ D*(1/η)^(4*N)*A i/((x1-x0)^a*(y1-y0)^b) := by
  classical
  obtain ⟨Dx,hDx,prepX⟩ := Preparation.open_component_preparation_power hDD (ι := ι) N KU KD
  have hex (a : Fin (N+1)) := Preparation.open_component_preparation_power hDD (ι := ι) (N-a.val) KV KD
  choose Dy hDy prepY using hex
  let Dy₀ : ℝ := 1 + ∑ a, Dy a
  let D := 2*Dx*Dy₀*2^(2*N)*(2*((N:ℝ)+1))^(2*N)
  have hDy0 : 1 ≤ Dy₀ := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => zero_le_one.trans (hDy j))
  have hDy_le (a : Fin (N+1)) : Dy a ≤ Dy₀ := by
    exact (Finset.single_le_sum (fun j _ => zero_le_one.trans (hDy j)) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hD : 1 ≤ D := by
    dsimp [D]
    have hN : (1 : ℝ) ≤ 2*((N:ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hDx) hDy0)
        (one_le_pow₀ (by norm_num))) (one_le_pow₀ hN)
  refine ⟨D,hD,?_⟩
  intro η hη hη1 f A x0 x1 y0 y1 U hx hy hU hsub hA hamp hfx hfy hKU hKV hmeas hbadmeas hcountX hcountY
  let L := x1-x0
  let W := y1-y0
  have hL : 0 < L := sub_pos.mpr hx
  have hW : 0 < W := sub_pos.mpr hy
  let ηx := η/2
  let ηy := η/(2*((N:ℝ)+1))
  have hηx : 0 < ηx := by dsimp [ηx]; positivity
  have hηy : 0 < ηy := by dsimp [ηy]; positivity
  have hηx1 : ηx ≤ 1 := by dsimp [ηx]; linarith
  have hηy1 : ηy ≤ 1 := by dsimp [ηy]; apply (div_le_iff₀ (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) N]
  let Cx := 2*Dx*(1/ηx)^(2*N)
  let C := D*(1/η)^(4*N)
  have hCx0 : 0 ≤ Cx := by dsimp [Cx]; positivity
  let V := horizontalGoodOn U f N A Cx L
  have hVsub : V ⊆ U := fun _ hp => hp.1
  have hxloss : volume (U \ V) ≤ ENNReal.ofReal (ηx*L*W) := by
    apply (Preparation.rectangle_section_budget_swap (q := ηx*L)
      (hU.measurableSet.diff (hmeas Cx)) (fun p hp => ⟨mem_univ _,(hsub hp.1).2⟩) ?_).trans_eq
    · rw [← ENNReal.ofReal_mul (mul_nonneg hηx.le hL.le)]
    intro y _
    let Uy := horizontalSection U y
    have hUy : IsOpen Uy := hU.preimage (continuous_id.prodMk continuous_const)
    have hUx : Uy ⊆ Ioo x0 x1 := fun z hz => (hsub hz).1
    have h := prepX ηx hηx hηx1 (fun i x => f i (x,y)) A x0 x1 Uy hx hUy hUx
      (hKU y).1 (hKU y).2 hA (fun i => hfx i y) (fun i x hx => hamp i (x,y) hx)
      (fun l r _ _ _ hh i n hn hnN T sign _ => hcountX i n hn hnN y l r T sign hh)
    apply (measure_mono ?_).trans h
    intro x hbad
    have hxU : (x,y) ∈ U := hbad.1
    refine ⟨hxU,?_⟩
    have hf : ¬ (∀ i (n : Fin (N+1)), 0 < A i → |Jet (f i) n.val 0 (x,y)| < Cx*A i/L^n.val) :=
      fun hg => hbad.2 ⟨hxU,hg⟩
    push_neg at hf
    obtain ⟨i,n,hi,hfail⟩ := hf
    refine ⟨i,n.val,by omega,?_⟩
    rw [← Preparation.horizontalJet_eq_iteratedDeriv (f i) n.val (x,y)]
    change (Dx*(1/ηx)^(2*N))*A i/L^n.val < |Jet (f i) n.val 0 (x,y)|
    have hp : 0 < (Dx*(1/ηx)^(2*N))*A i/L^n.val := by positivity
    apply lt_of_lt_of_le ?_ hfail
    have hEq : Cx*A i/L^n.val = 2*((Dx*(1/ηx)^(2*N))*A i/L^n.val) := by dsimp [Cx]; ring
    rw [hEq]
    linarith
  have hzero : ∀ i p, p ∈ U → A i = 0 → ∀ n ≤ N, Jet (f i) n 0 p = 0 := by
    intro i p hp hi n _
    exact horizontal_zero_of_open hU (fun z hz => by simpa [hi] using hamp i z hz) p hp n
  have hcoef (a : Fin (N+1)) : Dy a*(1/ηy)^(2*(N-a.val))*Cx ≤ C := by
    have hyinv : 1 ≤ 1/ηy := (one_le_div hηy).2 hηy1
    have hp := pow_le_pow_right₀ hyinv (show 2*(N-a.val) ≤ 2*N by omega)
    have hCeq : Dy₀*(1/ηy)^(2*N)*Cx = C := by
      have hxinv : 1/ηx = 2*(1/η) := by dsimp [ηx]; ring
      have hyinv' : 1/ηy = (2*((N:ℝ)+1))*(1/η) := by
        have hn : (2:ℝ)*((N:ℝ)+1) ≠ 0 := by positivity
        dsimp [ηy]
        field_simp
      dsimp only [Cx,C,D]
      rw [hxinv,hyinv',mul_pow,mul_pow,show 4*N = 2*N+2*N by omega,pow_add]
      ring
    rw [← hCeq]
    gcongr
    exact hDy_le a
  let bad (a : Fin (N+1)) := verticalBadOn V f N a.val A C L W
  have hbadV (a : Fin (N+1)) : bad a ⊆ V := fun _ hp => hp.1
  have hyLoss (a : Fin (N+1)) :
      volume (bad a) ≤ ENNReal.ofReal (ηy*W*L) := by
    apply (Preparation.rectangle_section_budget (q := ηy*W) (hbadmeas Cx C a.val)
      (fun p hp => ⟨(hsub (hVsub (hbadV a hp))).1,mem_univ _⟩) ?_).trans_eq
    · rw [← ENNReal.ofReal_mul (mul_nonneg hηy.le hW.le)]
    intro x _
    let Vx := verticalSection V x
    have hVx : Vx ⊆ verticalSection U x := fun _ hp => hVsub hp
    have hVxopen : IsOpen Vx := horizontalGoodOn_section_open U f N A Cx L x
      (hU.preimage (continuous_const.prodMk continuous_id))
      (fun i n hn => (hfy i n hn x).continuousOn)
    let B (i : ι) := Cx*A i/L^a.val
    have hB (i : ι) : 0 ≤ B i := div_nonneg (mul_nonneg hCx0 (hA i)) (pow_nonneg hL.le _)
    have hh := prepY a ηy hηy hηy1 (fun i y => Jet (f i) a.val 0 (x,y)) B y0 y1 Vx hy hVxopen
      (fun y hy => (hsub (hVx hy)).2) (hKV Cx x).1 (hKV Cx x).2 hB
      (fun i => (hfy i a.val (by omega) x).mono hVx)
      (fun i y hy => horizontalGoodOn_bound hA hzero hy i a.val (by omega))
      (fun l r _ _ _ hs i n hn hnN T sign _ => hcountY i a.val n hn (by omega) x l r T sign (hs.trans hVx))
    apply (measure_mono ?_).trans hh
    intro y hb
    obtain ⟨hyV,i,n,hn,hbad⟩ := hb
    refine ⟨hyV,i,n,hn,?_⟩
    have hscale : Dy a*(1/ηy)^(2*(N-a.val))*B i/W^n ≤ C*A i/(L^a.val*W^n) := by
      dsimp [B]
      have he : Dy a*(1/ηy)^(2*(N-a.val))*(Cx*A i/L^a.val)/W^n =
          (Dy a*(1/ηy)^(2*(N-a.val))*Cx)*A i/(L^a.val*W^n) := by ring
      rw [he]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcoef a) (hA i)) (by positivity)
    apply hscale.trans_lt
    change C*A i/(L^a.val*W^n) < |iteratedDeriv n (fun y => Preparation.horizontalJet (f i) a.val (x,y)) y|
    rw [← Preparation.mixedJet_eq_iteratedDeriv (f i) a.val n (x,y)]
    exact hbad
  let G := V \ ⋃ a, bad a
  have hG : MeasurableSet G := (hmeas Cx).diff (MeasurableSet.iUnion (fun a => hbadmeas Cx C a.val))
  refine ⟨G,hG,fun p hp => hVsub hp.1,?_,?_⟩
  · have hcov : U \ G ⊆ (U \ V) ∪ ⋃ a, bad a := by
      intro p hp
      by_cases hv : p ∈ V
      · right
        by_contra hh
        exact hp.2 ⟨hv,hh⟩
      · exact Or.inl ⟨hp.1,hv⟩
    calc
      _ ≤ volume ((U \ V) ∪ ⋃ a, bad a) := measure_mono hcov
      _ ≤ volume (U \ V)+volume (⋃ a, bad a) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ηx*L*W) + ∑ a, ENNReal.ofReal (ηy*W*L) :=
        add_le_add hxloss ((measure_iUnion_fintype_le volume _).trans (Finset.sum_le_sum fun a _ => hyLoss a))
      _ = ENNReal.ofReal (η*L*W) := by
        simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        dsimp [ηx,ηy]
        push_cast
        field_simp
        ring
  · intro p hp i a b hab
    apply le_of_not_gt
    intro h
    apply hp.2
    let j : Fin (N+1) := ⟨a,by omega⟩
    have hn : b ≤ N-j.val := by dsimp [j]; omega
    exact mem_iUnion.mpr ⟨j,hp.1,i,b,hn,h⟩

end PaperI.GoodStrips
