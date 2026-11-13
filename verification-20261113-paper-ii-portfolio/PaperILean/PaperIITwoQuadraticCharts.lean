import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Paper II, `low:6:so36:two-charts` (II4659–4669).
The coefficients are those of the actual quadratic graph in II4636. -/

namespace PaperII.TwoQuadraticCharts

noncomputable section

abbrev Endpoint := ℝ × ℝ × ℝ

abbrev Endpoint.r (p : Endpoint) : ℝ := p.1
abbrev Endpoint.B (p : Endpoint) : ℝ := p.2.1
abbrev Endpoint.e (p : Endpoint) : ℝ := p.2.2

def Endpoint.A (p : Endpoint) : ℝ := p.e * p.B + p.r * p.e ^ 2 / 2
def Endpoint.b (p : Endpoint) : ℝ := p.B + p.r * p.e
def Endpoint.C (p : Endpoint) : ℝ := p.r / 2

def conditionedEndpoints (P K : ℝ) : Set Endpoint :=
  {p | |p.r| ≤ P ^ K ∧ |p.B| ≤ P ^ K ∧ P ^ (-K) ≤ |p.B|}

def weightedEndpoints (P K σ : ℝ) : Set Endpoint :=
  {p | p ∈ conditionedEndpoints P K ∧ σ * (1 + |p.e|) ≤ |p.A|}

def gridEndpoints (P K σ : ℝ) : Set Endpoint :=
  {p | p ∈ conditionedEndpoints P K ∧ |p.A| < σ * (1 + |p.e|)}

private theorem quadratic_discriminant (p : Endpoint) :
    p.b ^ 2 - 4 * (p.A * p.C) = p.B ^ 2 := by
  simp only [Endpoint.A, Endpoint.b, Endpoint.C]
  ring

private theorem product_bound (p : Endpoint) {U σ : ℝ}
    (hU : 1 ≤ U) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (hr : |p.r| ≤ U) (hB : |p.B| ≤ U)
    (hgrid : |p.A| < σ * (1 + |p.e|)) : |p.A * p.C| ≤ 6 * U * σ := by
  have hU₀ : 0 ≤ U := by linarith
  by_cases hs : |p.e| ≤ 1
  · have hA : |p.A| ≤ 2 * σ :=
      hgrid.le.trans (by nlinarith [mul_nonneg hσ₀ (sub_nonneg.mpr hs)])
    have hC : |p.C| ≤ U / 2 := by
      simp only [Endpoint.C, abs_div, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num)]
      exact div_le_div_of_nonneg_right hr (by norm_num)
    calc
      |p.A * p.C| = |p.A| * |p.C| := abs_mul _ _
      _ ≤ (2 * σ) * (U / 2) := mul_le_mul hA hC (abs_nonneg _) (by positivity)
      _ ≤ 6 * U * σ := by nlinarith [mul_nonneg hU₀ hσ₀]
  · have he₁ : 1 ≤ |p.e| := le_of_lt (lt_of_not_ge hs)
    have he : p.e ≠ 0 := by
      intro he₀
      simp only [he₀, abs_zero] at he₁
      linarith
    have hquot : |p.A / p.e| ≤ 2 * σ := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr he)]
      calc
        |p.A| ≤ σ * (1 + |p.e|) := hgrid.le
        _ ≤ σ * (|p.e| + |p.e|) := mul_le_mul_of_nonneg_left (by linarith) hσ₀
        _ = 2 * σ * |p.e| := by ring
    have hdiff : |p.A / p.e - p.B| ≤ 3 * U :=
      (abs_sub _ _).trans (by linarith)
    have hprod : p.A * p.C = (p.A / p.e) * (p.A / p.e - p.B) := by
      simp only [Endpoint.A, Endpoint.C]
      field_simp [he]
      ring
    rw [hprod, abs_mul]
    calc
      |p.A / p.e| * |p.A / p.e - p.B| ≤ (2 * σ) * (3 * U) :=
        mul_le_mul hquot hdiff (abs_nonneg _) (by positivity)
      _ = 6 * U * σ := by ring

/-- A common threshold for every conditioned endpoint. The grid set is exactly
the complement of the weighted set inside the conditioned set. -/
theorem two_quadratic_charts (K δ : ℝ) (hδ : 0 < δ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ P : ℝ, 2 ≤ P →
      ∃ σ : ℝ, P ^ (-E) ≤ σ ∧
        weightedEndpoints P K σ ∪ gridEndpoints P K σ = conditionedEndpoints P K ∧
        Disjoint (weightedEndpoints P K σ) (gridEndpoints P K σ) ∧
        ∀ p ∈ gridEndpoints P K σ, |p.A * p.C| ≤ δ * p.b ^ 2 ∧ P ^ (-E) ≤ |p.b| := by
  let K₀ : ℝ := max K 0
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hK : K ≤ K₀ := le_max_left _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_min (by norm_num : (0 : ℝ) < 1 / 48) (div_pos hδ (by norm_num : (0 : ℝ) < 12)))
    (by norm_num : (1 / 2 : ℝ) < 1)
  let E : ℝ := 3 * K₀ + n
  refine ⟨E, by dsimp [E]; positivity, ?_⟩
  intro P hP
  have hP₀ : 0 < P := by linarith
  have hP₁ : 1 ≤ P := by linarith
  let U : ℝ := P ^ K₀
  let L : ℝ := P ^ (-K₀)
  let σ : ℝ := P ^ (-E)
  have hU : 1 ≤ U := Real.one_le_rpow hP₁ hK₀
  have hL₀ : 0 < L := Real.rpow_pos_of_pos hP₀ _
  have hL₁ : L ≤ 1 := by
    simpa [L] using Real.rpow_le_rpow_of_exponent_le hP₁ (neg_nonpos.mpr hK₀)
  have hσ₀ : 0 ≤ σ := (Real.rpow_pos_of_pos hP₀ _).le
  let q : ℝ := P ^ (-(n : ℝ))
  have hq : q ≤ min (1 / 48) (δ / 12) := by
    calc
      q ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hP (neg_nonpos.mpr (Nat.cast_nonneg n))
      _ = (1 / 2 : ℝ) ^ n := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, ← inv_pow, one_div]
      _ ≤ min (1 / 48) (δ / 12) := hn.le
  have hscale : U * σ = q * L ^ 2 := by
    dsimp [U, σ, E, q, L]
    rw [pow_two, ← mul_assoc, ← Real.rpow_add hP₀, ← Real.rpow_add hP₀,
      ← Real.rpow_add hP₀]
    congr 1
    ring
  have hscale₁ : U * σ ≤ (1 / 48) * L ^ 2 := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_right (hq.trans (min_le_left _ _)) (sq_nonneg _)
  have hscale₂ : U * σ ≤ (δ / 12) * L ^ 2 := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_right (hq.trans (min_le_right _ _)) (sq_nonneg _)
  have hσL : σ ≤ L / 2 := by
    have hσU : σ ≤ U * σ := by simpa using mul_le_mul_of_nonneg_right hU hσ₀
    have hLsq : L ^ 2 ≤ L := by nlinarith [mul_nonneg hL₀.le (sub_nonneg.mpr hL₁)]
    linarith
  have hσ₁ : σ ≤ 1 := by linarith
  refine ⟨σ, le_rfl, ?_, ?_, ?_⟩
  · ext p
    simp only [Set.mem_union, weightedEndpoints, gridEndpoints, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases le_or_gt (σ * (1 + |p.e|)) |p.A| with hw | hg
      · exact Or.inl ⟨hp, hw⟩
      · exact Or.inr ⟨hp, hg⟩
  · apply Set.disjoint_left.mpr
    intro p hw hg
    exact (not_lt_of_ge hw.2) hg.2
  · intro p hp
    have hr : |p.r| ≤ U := hp.1.1.trans (Real.rpow_le_rpow_of_exponent_le hP₁ hK)
    have hB : |p.B| ≤ U := hp.1.2.1.trans (Real.rpow_le_rpow_of_exponent_le hP₁ hK)
    have hBL : L ≤ |p.B| :=
      (Real.rpow_le_rpow_of_exponent_le hP₁ (neg_le_neg hK)).trans hp.1.2.2
    have hprod := product_bound p hU hσ₀ hσ₁ hr hB hp.2
    have hBsq : L ^ 2 ≤ p.B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hL₀.le (abs_nonneg p.B)).2 hBL
    have hdisc := quadratic_discriminant p
    have hbsq : L ^ 2 / 2 ≤ p.b ^ 2 := by
      have hAC : |p.A * p.C| ≤ L ^ 2 / 8 := by linarith
      linarith [neg_abs_le (p.A * p.C)]
    refine ⟨?_, ?_⟩
    · have hδsq := mul_le_mul_of_nonneg_left hbsq hδ.le
      linarith
    · have hlower : L / 2 ≤ |p.b| := by
        apply (sq_le_sq₀ (by positivity) (abs_nonneg p.b)).mp
        rw [sq_abs]
        nlinarith [sq_nonneg L]
      exact hσL.trans hlower

end

end PaperII.TwoQuadraticCharts
