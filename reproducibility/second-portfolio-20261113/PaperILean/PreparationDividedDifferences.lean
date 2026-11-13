import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! The one-variable interval estimate in I950. The only external input is
the equispaced specialization of de Boor (41), (44). It is a mean-value
identity, not a preparation or superlevel-length assumption. The manuscript's
signed-superlevel length bound is proved below from that identity. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

def equispacedDifference (j : ℕ) (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ (j - i) * (j.choose i : ℝ) * f (a + i * h)

/-- de Boor, *Divided differences*, equations (41) and (44), specialized
to distinct equispaced real nodes. No inhabitant is supplied. -/
structure PublishedEquispacedDividedDifferenceMeanValue : Prop where
  mean_value : ∀ (j : ℕ), 0 < j → ∀ (f : ℝ → ℝ) (a h : ℝ), 0 < h →
    ContDiffOn ℝ j f (Icc a (a + j * h)) →
    ∃ ξ ∈ Ioo a (a + j * h),
      h ^ j * iteratedDeriv j f ξ = equispacedDifference j f a h

theorem equispacedDifference_abs_le (j : ℕ) (f : ℝ → ℝ) (a h B : ℝ)
    (hf : ∀ i ∈ Finset.range (j + 1), |f (a + i * h)| ≤ B) :
    |equispacedDifference j f a h| ≤ (2 : ℝ) ^ j * B := by
  unfold equispacedDifference
  calc
    |∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ (j-i) * (j.choose i : ℝ) * f (a+i*h)|
        ≤ ∑ i ∈ Finset.range (j + 1),
          |(-1 : ℝ) ^ (j-i) * (j.choose i : ℝ) * f (a+i*h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [abs_mul, abs_pow] using
        mul_le_mul_of_nonneg_left (hf i hi) (Nat.cast_nonneg (j.choose i) : (0 : ℝ) ≤ _)
    _ = (2 : ℝ) ^ j * B := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose j

theorem published_signed_derivative_spacing_bound
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j : ℕ) (hj : 0 < j) (f : ℝ → ℝ) (a h B M σ : ℝ)
    (hh : 0 < h) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ j f (Icc a (a + j*h)))
    (hamp : ∀ x ∈ Icc a (a + j*h), |f x| ≤ B)
    (hderiv : ∀ x ∈ Ioo a (a + j*h), M ≤ σ * iteratedDeriv j f x) :
    M * h ^ j ≤ (2 : ℝ) ^ j * B := by
  obtain ⟨ξ,hξ,heq⟩ := hDD.mean_value j hj f a h hh hsmooth
  have hb : |equispacedDifference j f a h| ≤ (2 : ℝ)^j * B := by
    apply equispacedDifference_abs_le
    intro i hi
    have hij : (i : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply hamp
    constructor
    · have hn : (0 : ℝ) ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg i) hh.le
      linarith
    · nlinarith
  have hm : M ≤ |iteratedDeriv j f ξ| := by
    calc
      M ≤ σ * iteratedDeriv j f ξ := hderiv ξ hξ
      _ ≤ |σ * iteratedDeriv j f ξ| := le_abs_self _
      _ = |iteratedDeriv j f ξ| := by rw [abs_mul,hσ,one_mul]
  calc
    M * h^j ≤ |iteratedDeriv j f ξ| * h^j := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = |equispacedDifference j f a h| := by rw [← heq,abs_mul,abs_of_pos (pow_pos hh j)]; ring
    _ ≤ (2 : ℝ)^j * B := hb

/-- The interval may be open and may meet a singular branch endpoint. The
closed inner half supplies all nodes without imposing smoothness at u or v. -/
theorem published_signed_derivative_interval_bound
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j : ℕ) (hj : 0 < j) (f : ℝ → ℝ) (u v B M σ : ℝ)
    (huv : u < v) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ j f (Ioo u v))
    (hamp : ∀ x ∈ Ioo u v, |f x| ≤ B)
    (hderiv : ∀ x ∈ Ioo u v, M ≤ σ * iteratedDeriv j f x) :
    M * (v-u)^j ≤ (4 * (j : ℝ))^j * B := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  let a := u + (v-u)/4
  let h := (v-u)/(2*(j:ℝ))
  have hh : 0 < h := div_pos (sub_pos.mpr huv) (by positivity)
  have hjh : (j:ℝ)*h = (v-u)/2 := by dsimp [h]; field_simp; ring
  have hsub : Icc a (a+j*h) ⊆ Ioo u v := by
    intro x hx
    dsimp [a] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hb := published_signed_derivative_spacing_bound hDD j hj f a h B M σ hh hσ
    (hsmooth.mono hsub) (fun x hx => hamp x (hsub hx))
    (fun x hx => hderiv x (hsub ⟨hx.1.le,hx.2.le⟩))
  have hlen : v-u = (2*(j:ℝ))*h := by linarith [hjh]
  calc
    M * (v-u)^j = (2*(j:ℝ))^j * (M*h^j) := by rw [hlen,mul_pow]; ring
    _ ≤ (2*(j:ℝ))^j * ((2:ℝ)^j*B) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4*(j:ℝ))^j*B := by rw [← mul_assoc,← mul_pow]; congr 2; ring

theorem published_signed_derivative_spacing_strict_bound
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j : ℕ) (hj : 0 < j) (f : ℝ → ℝ) (a h B M σ : ℝ)
    (hh : 0 < h) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ j f (Icc a (a + j*h)))
    (hamp : ∀ x ∈ Icc a (a + j*h), |f x| ≤ B)
    (hderiv : ∀ x ∈ Ioo a (a + j*h), M < σ * iteratedDeriv j f x) :
    M * h ^ j < (2 : ℝ) ^ j * B := by
  obtain ⟨ξ,hξ,heq⟩ := hDD.mean_value j hj f a h hh hsmooth
  have hb : |equispacedDifference j f a h| ≤ (2 : ℝ)^j * B := by
    apply equispacedDifference_abs_le
    intro i hi
    have hij : (i : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    apply hamp
    constructor
    · have hn : (0 : ℝ) ≤ (i : ℝ)*h := mul_nonneg (Nat.cast_nonneg i) hh.le
      linarith
    · nlinarith
  have hm : M < |iteratedDeriv j f ξ| := by
    calc
      M < σ * iteratedDeriv j f ξ := hderiv ξ hξ
      _ ≤ |σ * iteratedDeriv j f ξ| := le_abs_self _
      _ = |iteratedDeriv j f ξ| := by rw [abs_mul,hσ,one_mul]
  calc
    M*h^j < |iteratedDeriv j f ξ| *h^j := mul_lt_mul_of_pos_right hm (pow_pos hh j)
    _ = |equispacedDifference j f a h| := by rw [← heq,abs_mul,abs_of_pos (pow_pos hh j)]; ring
    _ ≤ (2 : ℝ)^j*B := hb

theorem published_signed_derivative_interval_strict_bound
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j : ℕ) (hj : 0 < j) (f : ℝ → ℝ) (u v B M σ : ℝ)
    (huv : u < v) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ j f (Ioo u v))
    (hamp : ∀ x ∈ Ioo u v, |f x| ≤ B)
    (hderiv : ∀ x ∈ Ioo u v, M < σ * iteratedDeriv j f x) :
    M*(v-u)^j < (4*(j:ℝ))^j*B := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  let a := u+(v-u)/4
  let h := (v-u)/(2*(j:ℝ))
  have hh : 0 < h := div_pos (sub_pos.mpr huv) (by positivity)
  have hjh : (j:ℝ)*h = (v-u)/2 := by dsimp [h]; field_simp; ring
  have hsub : Icc a (a+j*h) ⊆ Ioo u v := by
    intro x hx
    dsimp [a] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hb := published_signed_derivative_spacing_strict_bound hDD j hj f a h B M σ hh hσ
    (hsmooth.mono hsub) (fun x hx => hamp x (hsub hx))
    (fun x hx => hderiv x (hsub ⟨hx.1.le,hx.2.le⟩))
  have hlen : v-u = (2*(j:ℝ))*h := by linarith [hjh]
  calc
    M*(v-u)^j = (2*(j:ℝ))^j*(M*h^j) := by rw [hlen,mul_pow]; ring
    _ < (2*(j:ℝ))^j*((2:ℝ)^j*B) := mul_lt_mul_of_pos_left hb (by positivity)
    _ = (4*(j:ℝ))^j*B := by rw [← mul_assoc,← mul_pow]; congr 2; ring

/-- A homogeneous threshold yields a component shorter than δ L. Zero
amplitude is covered without cancellation: the strict superlevel is then
incompatible with a nonempty component by the preceding strict estimate. -/
theorem published_signed_superlevel_interval_length
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (j : ℕ) (hj : 0 < j) (f : ℝ → ℝ) (u v B δ L σ : ℝ)
    (huv : u < v) (hB : 0 ≤ B) (hδ : 0 < δ) (hL : 0 < L) (hσ : |σ| = 1)
    (hsmooth : ContDiffOn ℝ j f (Ioo u v))
    (hamp : ∀ x ∈ Ioo u v, |f x| ≤ B)
    (hderiv : ∀ x ∈ Ioo u v,
      (4*(j:ℝ))^j * B / (δ*L)^j < σ * iteratedDeriv j f x) :
    v-u < δ*L := by
  have hb := published_signed_derivative_interval_strict_bound hDD j hj f u v B
    ((4*(j:ℝ))^j*B/(δ*L)^j) σ huv hσ hsmooth hamp hderiv
  have hp : 0 < (δ*L)^j := pow_pos (mul_pos hδ hL) j
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hcoef : 0 ≤ (4*(j:ℝ))^j*B := mul_nonneg (by positivity) hB
  have hx : (v-u)^j < (δ*L)^j := by
    by_contra hn
    have hx' : (δ*L)^j ≤ (v-u)^j := le_of_not_gt hn
    have he : (4*(j:ℝ))^j*B = ((4*(j:ℝ))^j*B/(δ*L)^j)*(δ*L)^j := by
      rw [div_mul_cancel₀ _ (ne_of_gt hp)]
    have hh := mul_le_mul_of_nonneg_left hx' (div_nonneg hcoef hp.le)
    rw [← he] at hh
    exact (not_lt_of_ge hh) hb
  exact (pow_lt_pow_iff_left₀ (sub_nonneg.mpr huv.le) (mul_pos hδ hL).le (Nat.ne_of_gt hj)).mp hx

theorem preparation_order_zero_bound (f : ℝ → ℝ) (I : Set ℝ) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 1 ≤ C) (hf : ∀ x ∈ I, |f x| ≤ B) :
    ∀ x ∈ I, |iteratedDeriv 0 f x| ≤ C*B := by
  intro x hx
  simpa only [iteratedDeriv_zero] using (hf x hx).trans (by nlinarith : B ≤ C*B)

end PaperI
