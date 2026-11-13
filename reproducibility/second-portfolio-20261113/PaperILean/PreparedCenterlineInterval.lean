import PaperILean.RegularCenterlineInterval
import PaperILean.CenteredGraphFormat
import PaperILean.PreparationGoodComponents
import PaperILean.OriginalPreparationFiniteList
import PaperILean.OpenComponentIntervals

/-! Select a closed interval inside the actual simultaneous derivative good
set. A strict margin makes that set open; its uniform component bound comes
from the checked Hardt application. Positive amplitude is explicit in the
intermediate lemma and will be supplied by the positive interval length. -/

noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem exists_closed_interval_of_open_component_mass {U : Set ℝ} {a b M : ℝ}
    (ho : IsOpen U) (hsub : U ⊆ Ioo a b) (hM : 0 < M)
    [Finite (ConnectedComponents U)] {K : ℕ}
    (hK : Nat.card (ConnectedComponents U) ≤ K) (hmass : M ≤ volume.real U) :
    ∃ u v : ℝ, u < v ∧ Icc u v ⊆ U ∧ M/(2*((K : ℝ)+1)) ≤ v-u := by
  classical
  letI := Fintype.ofFinite (ConnectedComponents U)
  obtain ⟨l,r,hparts,hcover⟩ := open_set_component_intervals ho hsub
  have hmass' : M ≤ volume.real (⋃ i ∈ (Finset.univ : Finset (ConnectedComponents U)),
      Ioo (l i) (r i)) := by simpa only [Finset.mem_univ,iUnion_true,← hcover] using hmass
  have hcard : (Finset.univ : Finset (ConnectedComponents U)).card ≤ K+1 := by
    simpa only [Finset.card_univ,← Nat.card_eq_fintype_card] using hK.trans (Nat.le_succ K)
  obtain ⟨i,_,u,v,huv,hinside,hlen,hgood⟩ := preparation_retained_closed_interval
    Finset.univ l r (fun x => x ∈ U) hM (Nat.succ_pos K) hcard hmass'
    (fun i _ x hx => (hparts i).2.2.2 hx)
  exact ⟨u,v,huv,hgood,by simpa only [Nat.cast_succ] using hlen⟩

theorem preparation_half_good_mass {G : Set ℝ} {a b : ℝ} (hab : a < b)
    (hGm : MeasurableSet G) (hGsub : G ⊆ Ioo a b)
    (hbad : volume (Ioo a b \ G) ≤ ENNReal.ofReal ((b-a)/2)) :
    (b-a)/2 ≤ volume.real G := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  rw [ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num))] at hb
  change volume.real (Ioo a b \ G) ≤ (b-a)/2 at hb
  rw [measureReal_diff hGsub hGm (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top),
    Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr hab.le)] at hb
  linarith

theorem published_bounded_format_prepared_closed_interval
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (B a b : ℝ), 0 < B → a < b →
      (∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x) →
      ContDiffOn ℝ N f (Ioo a b) → (∀ x ∈ Ioo a b, |f x| ≤ B) →
      ∃ u v : ℝ, u < v ∧ Icc u v ⊆ Ioo a b ∧ (b-a)/(K : ℝ) ≤ v-u ∧
        ∀ x ∈ Icc u v, ∀ n ≤ N, |iteratedDeriv n f x| ≤ C*B/(b-a)^n := by
  obtain ⟨C,hC,hprep⟩ := published_bounded_format_finite_list_preparation
    (ι := Unit) hDD hCell hHardt hQE s D N (1/2) (by norm_num)
  obtain ⟨K,hcount⟩ := published_bounded_format_strictDerivativeGoodSet_components
    hCell hHardt hQE s D N
  refine ⟨2*C,by linarith,4*(K+1),by omega,?_⟩
  intro A S hc hd hS f B a b hB hab hrep hf hamp
  obtain ⟨G,hGm,hGsub,hbad,hgood⟩ := hprep (fun _ => A) (fun _ => S)
    (fun _ => hc) (fun _ => hd) (fun _ => hS) (fun _ => f) (fun _ => B)
    a b hab (fun _ => hrep) (fun _ => hf) (fun _ => hamp)
  let T : Fin (N+1) → ℝ := fun n => 2*C*B/(b-a)^n.val
  let U := strictDerivativeGoodSet f N a b T
  have hUsub : U ⊆ Ioo a b := fun _ hx => hx.1
  have hGU : G ⊆ U := by
    intro x hx
    refine ⟨hGsub hx,?_⟩
    intro n
    have hp : 0 < C*B/(b-a)^n.val :=
      div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hC) hB) (pow_pos (sub_pos.mpr hab) _)
    have hg := hgood x hx () n.val (Nat.lt_succ_iff.mp n.isLt)
    change |iteratedDeriv n.val f x| < 2*C*B/(b-a)^n.val
    calc
      _ ≤ C*B/(b-a)^n.val := hg
      _ < 2*(C*B/(b-a)^n.val) := by linarith
      _ = 2*C*B/(b-a)^n.val := by ring
  have hUfinite : volume U ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono hUsub)
  have hmass : (b-a)/2 ≤ volume.real U :=
    (preparation_half_good_mass hab hGm hGsub (by convert hbad using 2 <;> ring)).trans
      (measureReal_mono hGU hUfinite)
  have hcomp := hcount A S hc hd hS f a b T hrep hf
  letI : Finite (ConnectedComponents U) := hcomp.1
  obtain ⟨u,v,huv,hsub,hlen⟩ := exists_closed_interval_of_open_component_mass
    (isOpen_strictDerivativeGoodSet hf T) hUsub
    (div_pos (sub_pos.mpr hab) (by norm_num)) hcomp.2 hmass
  refine ⟨u,v,huv,hsub.trans hUsub,?_,?_⟩
  · have he : ((4*(K+1) : ℕ) : ℝ) = 2*(2*((K : ℝ)+1)) := by push_cast; ring
    rw [he]
    simpa only [div_div] using hlen
  · intro x hx n hn
    exact ((hsub hx).2 ⟨n,Nat.lt_succ_iff.mpr hn⟩).le

/-- Comparison with the original longitudinal scale; the constant is independent
of the selected regular interval and of the derivative order below `N`. -/
theorem preparation_derivative_scale_comparison {C B L ell : ℝ} {K N n : ℕ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hL : 0 < L) (hK : 0 < K)
    (hlen : L/(K : ℝ) ≤ ell) (hn : n ≤ N) :
    C*B/ell^n ≤ (C*(K : ℝ)^N)*B/L^n := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hell : 0 < ell := (div_pos hL hKr).trans_le hlen
  have hLe : L ≤ (K : ℝ)*ell := by
    simpa only [mul_comm] using (div_le_iff₀ hKr).mp hlen
  have hp : L^n ≤ (K : ℝ)^N*ell^n := calc
    L^n ≤ ((K : ℝ)*ell)^n := pow_le_pow_left₀ hL.le hLe n
    _ = (K : ℝ)^n*ell^n := mul_pow _ _ _
    _ ≤ (K : ℝ)^N*ell^n := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hK1 hn) (pow_nonneg hell.le n)
  apply (div_le_div_iff₀ (pow_pos hell n) (pow_pos hL n)).mpr
  convert mul_le_mul_of_nonneg_left hp (mul_nonneg hC hB) using 1 <;> ring

/-- Apply the original preparation route to the actual Lipschitz centerline.
Only the auxiliary scalar is centered; the geometric function is unchanged.
Reconstructed after checkpoint128's unsaved final files were pruned. -/
theorem published_bounded_format_lipschitz_prepared_interval
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPiece : PublishedPiecewiseNashExtensions) (s D N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Icc a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x) →
      LipschitzOnWith 1 f (Icc a b) →
      ∃ u v : ℝ, u < v ∧ Icc u v ⊆ Icc a b ∧ (b-a)/(K : ℝ) ≤ v-u ∧
        AnalyticOnNhd ℝ f (Icc u v) ∧
        (∀ x ∈ Icc u v, ∀ n ≤ N,
          |iteratedDeriv n (fun q => f q-f a) x| ≤ C*(b-a)/(b-a)^n) ∧
        (∀ x ∈ Icc u v, ∀ n, 0 < n → n ≤ N →
          |iteratedDeriv n f x| ≤ C*(b-a)/(b-a)^n) := by
  obtain ⟨KA,hKA,hregular⟩ := published_bounded_format_long_analytic_interval
    hCell hHardt hQE hPiece s D
  obtain ⟨C,hC,KG,hKG,hprepare⟩ := published_bounded_format_prepared_closed_interval
    hDD hCell hHardt hQE s D N
  have hKA1 : 1 ≤ (KA : ℝ) := by exact_mod_cast hKA
  have hconstant : 1 ≤ C*(KA : ℝ)^N := calc
    1 ≤ C := hC
    _ = C*1 := by ring
    _ ≤ C*(KA : ℝ)^N := mul_le_mul_of_nonneg_left
      (one_le_pow₀ hKA1) (zero_le_one.trans hC)
  refine ⟨C*(KA : ℝ)^N,hconstant,KA*KG,
    Nat.mul_pos hKA hKG,?_⟩
  intro A S hc hd hS f a b hab hrep hLip
  obtain ⟨l,r,hal,hlr,hrb,hlen,hA⟩ := hregular A S hc hd hS f a b hab hrep
  have hsub : Ioo l r ⊆ Icc a b := fun _ hx =>
    ⟨hal.trans hx.1.le,hx.2.le.trans hrb⟩
  obtain ⟨B,hBc,hBd,hB⟩ := centeredGraphRelation_bounded_format A S s D hc hd hS (f a)
  obtain ⟨u,v,huv,huvsub,hvlen,hgood⟩ := hprepare B (centeredGraphRelation S (f a))
    hBc hBd hB (fun q => f q-f a) (b-a) l r (sub_pos.mpr hab) hlr
    (fun x hx y => centeredGraphRelation_realize_iff S f (Icc a b) hrep (f a) x y (hsub hx))
    (centered_contDiffOn hA.contDiffOn_of_completeSpace a)
    (fun x hx => centered_one_lipschitz_amplitude hLip ⟨le_rfl,hab.le⟩ (hsub hx))
  have hfull : (b-a)/((KA*KG : ℕ) : ℝ) ≤ v-u := calc
    _ = ((b-a)/(KA : ℝ))/(KG : ℝ) := by rw [Nat.cast_mul,div_div]
    _ ≤ (r-l)/(KG : ℝ) := div_le_div_of_nonneg_right hlen (Nat.cast_nonneg KG)
    _ ≤ v-u := hvlen
  have hbound : ∀ x ∈ Icc u v, ∀ n ≤ N,
      |iteratedDeriv n (fun q => f q-f a) x| ≤ (C*(KA : ℝ)^N)*(b-a)/(b-a)^n := by
    intro x hx n hn
    exact (hgood x hx n hn).trans (preparation_derivative_scale_comparison
      (zero_le_one.trans hC) (sub_nonneg.mpr hab.le) (sub_pos.mpr hab) hKA hlen hn)
  refine ⟨u,v,huv,huvsub.trans hsub,hfull,hA.mono huvsub,hbound,?_⟩
  intro x hx n hn hN
  rw [← iteratedDeriv_centered f a x n hn]
  exact hbound x hx n hN

end PaperI
