import PaperILean.PreparedCenterlineInterval
import PaperILean.CoordinatePathFormat

/-! I1263: algebraic scale conversion and actual Euclidean coordinate spans.
The n=0 comparison needs ell <= L. No absolute centerline-height bound is
inferred from a Lipschitz bound. Pre-strategy: checkpoint_133_pre_strategy. -/

noncomputable section
namespace PaperI
open Set

theorem prepared_arc_scale_constant_ge_one {C c : ℝ} (hC : 1 ≤ C)
    (hc : 1 ≤ c) (N : ℕ) : 1 ≤ C*c^N := by
  calc
    1 ≤ C := hC
    _ = C*1 := by ring
    _ ≤ C*c^N := mul_le_mul_of_nonneg_left (one_le_pow₀ hc) (zero_le_one.trans hC)

/-- The amplitude and denominator are both transferred to L. The loss c^N
is independent of the particular derivative n <= N. -/
theorem prepared_arc_derivative_scale_comparison {C c L ell : ℝ} {N n : ℕ}
    (hC : 0 ≤ C) (hc : 1 ≤ c) (hell : 0 < ell) (hellL : ell ≤ L)
    (hspan : L ≤ c*ell) (hn : n ≤ N) :
    C*ell/ell^n ≤ (C*c^N)*L/L^n := by
  have hL : 0 < L := hell.trans_le hellL
  have hp : L^n ≤ c^N*ell^n := calc
    L^n ≤ (c*ell)^n := pow_le_pow_left₀ hL.le hspan n
    _ = c^n*ell^n := mul_pow _ _ _
    _ ≤ c^N*ell^n := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hc hn) (pow_nonneg hell.le n)
  have hden : C*ell/ell^n ≤ (C*c^N)*ell/L^n := by
    apply (div_le_div_iff₀ (pow_pos hell n) (pow_pos hL n)).mpr
    convert mul_le_mul_of_nonneg_left hp (mul_nonneg hC hell.le) using 1 <;> ring
  exact hden.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hellL (mul_nonneg hC (pow_nonneg (zero_le_one.trans hc) N)))
    (pow_nonneg hL.le n))

theorem signed_coordinate_span_le_euclidean_diameter {κ : Type*} [Fintype κ]
    (S : Set (κ → ℝ))
    (hS : Bornology.IsBounded ((WithLp.equiv 2 (κ → ℝ)).symm '' S))
    (i : κ) {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (x : κ → ℝ) (hx : x ∈ S) (y : κ → ℝ) (hy : y ∈ S) :
    σ*y i-σ*x i ≤ Metric.diam ((WithLp.equiv 2 (κ → ℝ)).symm '' S) := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using
      (le_abs_self (y i-x i)).trans (coordinate_range_le_euclidean_diameter S hS i y hy x hx)
  · have h := (le_abs_self (x i-y i)).trans
      (coordinate_range_le_euclidean_diameter S hS i x hx y hy)
    linarith

theorem monotone_subdivision_time_mem_unit {t : ℕ → ℝ} {n j : ℕ}
    (h0 : t 0=0) (hn : t n=1) (hm : MonotoneOn t (Icc 0 n)) (hj : j ≤ n) :
    t j ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [h0] using hm (show 0 ∈ Icc 0 n by simp)
      ⟨Nat.zero_le j,hj⟩ (Nat.zero_le j)
  · simpa only [hn] using hm ⟨Nat.zero_le j,hj⟩
      (show n ∈ Icc 0 n by simp) hj

end PaperI
