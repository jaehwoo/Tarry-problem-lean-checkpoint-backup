import PaperILean.PreparationOpenComponents

noncomputable section
namespace PaperI.Preparation

open Set MeasureTheory
open scoped ENNReal

/-- The open-component estimate with its explicit polynomial loss dependence. -/
theorem open_component_preparation_power
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N KU KD : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (f : ι → ℝ → ℝ) (B : ι → ℝ) (a b : ℝ) (U : Set ℝ),
      a < b → IsOpen U → U ⊆ Ioo a b →
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
        (D * (1/ε)^(2*N)) * B i / (b-a)^n < |iteratedDeriv n (f i) x|} ≤
        ENNReal.ofReal (ε * (b-a)) := by
  classical
  let k : ℝ := (KU : ℝ) + 1
  let den : ℝ := 2 * ((KD : ℝ)+1) * ((N : ℝ)+1) * ((Fintype.card ι : ℝ)+1)
  let A : ℝ := 1 + 4 * (N : ℝ) * den
  let D : ℝ := A^N * k^(2*N)
  have hk : 1 ≤ k := by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) KU]
  have hden : 1 ≤ den := by
    dsimp [den]
    have h1 : (1 : ℝ) ≤ (KD : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) KD]
    have h2 : (1 : ℝ) ≤ (N : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have h3 : (1 : ℝ) ≤ (Fintype.card ι : ℝ)+1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) h1) h2) h3
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  refine ⟨D,one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ hk),?_⟩
  intro ε hε hε₁ f B a b U hab ho hsub hfinite hKU hB hsmooth hamp hcount
  letI := hfinite
  let δ : ℝ := ε/k
  let r : ℝ := δ/den
  let C : ℝ := (A/δ)^N
  let S : ℝ := (1/δ)^N
  have hδ : 0 < δ := div_pos hε (zero_lt_one.trans_le hk)
  have hδ₁ : δ ≤ 1 := (div_le_iff₀ (zero_lt_one.trans_le hk)).mpr (by simpa using hε₁.trans hk)
  have hq : 1 ≤ 1/δ := (one_le_div hδ).2 hδ₁
  have hr : 0 < r := div_pos hδ (zero_lt_one.trans_le hden)
  have hAδ : 1 ≤ A/δ := (one_le_div hδ).2 (hδ₁.trans hA)
  have hC : 1 ≤ C := one_le_pow₀ hAδ
  have hCS : C*S = D*(1/ε)^(2*N) := by
    have hδinv : 1/δ = k*(1/ε) := by
      dsimp [δ]
      field_simp
    calc
      C*S = A^N * (1/δ)^(2*N) := by
        dsimp [C,S]
        rw [two_mul,pow_add,div_eq_mul_inv,mul_pow]
        simp only [one_div]
        ring
      _ = D*(1/ε)^(2*N) := by
        rw [hδinv,mul_pow]
        simp [D,mul_assoc]
  let E := {x | x ∈ U ∧ ∃ i, ∃ n ≤ N,
    (D * (1/ε)^(2*N)) * B i / (b-a)^n < |iteratedDeriv n (f i) x|}
  have hL : 0 < b-a := sub_pos.mpr hab
  have hbudget := volume_subset_component_budget (E := E) ho hsub
    (fun _ hx => hx.1) hKU (mul_nonneg hδ.le hL.le) (fun u v hau huv hvb hU => by
      have hlen : v-u ≤ b-a := by linarith
      by_cases hshort : v-u ≤ δ*(b-a)
      · exact (measure_mono inter_subset_right).trans
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal hshort)
      let F : ι × Fin (N+1) → Set ℝ := fun j =>
        {x | x ∈ Ioo u v ∧ C * B j.1 / (v-u)^j.2.val <
          |iteratedDeriv j.2.val (f j.1) x|}
      have hcov : E ∩ Ioo u v ⊆ ⋃ j, F j := by
        rintro x ⟨⟨hxU,i,n,hn,hbad⟩,hx⟩
        have hscale := component_threshold_le n hδ hL (le_of_not_ge hshort)
          (zero_le_one.trans hC) (hB i) (show (1/δ)^n ≤ S from pow_le_pow_right₀ hq hn)
        rw [hCS] at hscale
        exact mem_iUnion.mpr ⟨(i,⟨n,Nat.lt_succ_iff.mpr hn⟩),hx,hscale.trans_lt hbad⟩
      have hF (j : ι × Fin (N+1)) : volume (F j) ≤ ENNReal.ofReal (2*(KD : ℝ)*r*(v-u)) := by
        let n := j.2.val
        have hn : n ≤ N := Nat.lt_succ_iff.mp j.2.isLt
        by_cases hz : n=0
        · have hFempty : F j = ∅ := by
            ext x
            simp only [F, ← show n = j.2.val from rfl, hz, iteratedDeriv_zero, pow_zero, div_one,
              mem_setOf_eq, mem_empty_iff_false, iff_false]
            rintro ⟨hx,hbad⟩
            exact (not_lt_of_ge ((hamp j.1 x (hU hx)).trans
              (le_mul_of_one_le_left (hB j.1) hC))) hbad
          rw [hFempty,measure_empty]
          exact bot_le
        have hbase : 4*(n:ℝ)/r ≤ A/δ := by
          have hn' : (n:ℝ) ≤ N := by exact_mod_cast hn
          have hm : 4*(n:ℝ)*den ≤ A := by dsimp [A]; nlinarith [mul_nonneg (sub_nonneg.mpr hn') (zero_le_one.trans hden)]
          have heq : 4*(n:ℝ)/r = (4*(n:ℝ)*den)/δ := by dsimp [r]; field_simp
          rw [heq]
          exact div_le_div_of_nonneg_right hm hδ.le
        have hpow : (4*(n:ℝ)/r)^n ≤ C :=
          (pow_le_pow_left₀ (by positivity) hbase _).trans (pow_le_pow_right₀ hAδ hn)
        exact published_abs_derivative_superlevel_volume_le hDD n N KD (f j.1) u v
          (B j.1) r C (Nat.pos_of_ne_zero hz) hn huv (hB j.1) hr hpow
          ((hsmooth j.1).mono hU) (fun x hx => hamp j.1 x (hU hx))
          (fun sign hs => hcount u v hau huv hvb hU j.1 n (Nat.pos_of_ne_zero hz) hn _ sign hs)
      have hcoef : ((Fintype.card ι : ℝ) * ((N : ℝ)+1)) * 2 * (KD : ℝ) ≤ den := by
        calc
          _ = 2*(KD : ℝ)*((N : ℝ)+1)*(Fintype.card ι : ℝ) := by ring
          _ ≤ den := by
            dsimp [den]
            gcongr <;> linarith
      have hscaled : ((Fintype.card ι : ℝ) * ((N : ℝ)+1)) * 2 * (KD : ℝ) * r ≤ δ := by
        calc
          _ ≤ den * r := mul_le_mul_of_nonneg_right hcoef hr.le
          _ = δ := by dsimp [r]; field_simp
      calc
        volume (E ∩ Ioo u v) ≤ volume (⋃ j, F j) := measure_mono hcov
        _ ≤ ∑ j, volume (F j) := measure_iUnion_fintype_le volume _
        _ ≤ ∑ _j : ι × Fin (N+1), ENNReal.ofReal (2*(KD : ℝ)*r*(v-u)) :=
          Finset.sum_le_sum fun j _ => hF j
        _ = ENNReal.ofReal
            ((((Fintype.card ι : ℝ)*((N : ℝ)+1))*2*(KD : ℝ)*r)*(v-u)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by
            exact mul_nonneg (mul_nonneg (by positivity) hr.le) (sub_nonneg.mpr huv.le))]
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
        _ ≤ ENNReal.ofReal (δ*(b-a)) := ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_right hscaled (sub_nonneg.mpr huv.le)).trans
            (mul_le_mul_of_nonneg_left hlen hδ.le)))
  have hcoef : (KU : ℝ)*δ ≤ ε := by
    dsimp [δ,k]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  exact hbudget.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

end PaperI.Preparation
