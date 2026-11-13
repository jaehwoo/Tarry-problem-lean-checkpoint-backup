import PaperILean.GoodStripQuantitative

noncomputable section

namespace PaperI.GoodStrips

open Set MeasureTheory
open scoped ENNReal

private theorem rect_volume {x0 x1 y0 y1 : ℝ} (hx : x0<x1) :
    volume (Rect x0 x1 y0 y1) = ENNReal.ofReal ((x1-x0)*(y1-y0)) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hx.le)]

/-- The two ambient area conclusions from the nested quantitative loss
estimate. The loss theorem is supplied by the actual preparation proof. -/
theorem rect_loss_and_partial_bounds
    {ι : Type} (N : ℕ) (D : ℝ) (hD : 0≤D)
    (f : ι → ℝ × ℝ → ℝ) (A : ι → ℝ) (hA : ∀ i, 0≤A i)
    (x0 x1 y0 y1 : ℝ) (hx : x0<x1) (hy : y0<y1)
    (S : Set (ℝ × ℝ)) (hSsub : S⊆Rect x0 x1 y0 y1)
    (prep : ∀ (η : ℝ), 0<η → η≤1 → ∃ G : Set (ℝ × ℝ),
      MeasurableSet G ∧ G⊆S ∧
      volume (S\G)≤ENNReal.ofReal (η*(x1-x0)*(y1-y0)) ∧
      ∀ p∈G, ∀ i a b, a+b≤N →
        |Jet (f i) a b p|≤D*(1/η)^(4*N)*A i/((x1-x0)^a*(y1-y0)^b)) :
    (∀ ε : ℝ, 0<ε → ∃ G : Set (ℝ × ℝ), MeasurableSet G ∧ G⊆S ∧
      volume (S\G)≤ENNReal.ofReal (ε*(x1-x0)*(y1-y0)) ∧
      ∀ p∈G, ∀ i a b, a+b≤N →
        |Jet (f i) a b p|≤D*(1/min ε 1)^(4*N)*A i/((x1-x0)^a*(y1-y0)^b)) ∧
    (∀ q : ℝ, 0<q → q≤1 →
      ENNReal.ofReal q * volume (Rect x0 x1 y0 y1) ≤ volume S →
      ∃ G : Set (ℝ × ℝ), MeasurableSet G ∧ G⊆S ∧
        ENNReal.ofReal ((1/2)*q^(max 1 (4*N))*(x1-x0)*(y1-y0)) ≤ volume G ∧
        ∀ p∈G, ∀ i a b, a+b≤N →
          |Jet (f i) a b p|≤
            (D*2^(4*N))*(1/q)^(max 1 (4*N))*A i/((x1-x0)^a*(y1-y0)^b)) := by
  have hL : 0≤x1-x0 := sub_nonneg.mpr hx.le
  have _hSfinite : volume S ≠ ⊤ := ne_top_of_le_ne_top (by rw [rect_volume hx]; exact ENNReal.ofReal_ne_top)
    (measure_mono hSsub)
  have hW : 0≤y1-y0 := sub_nonneg.mpr hy.le
  constructor
  · intro ε hε
    obtain ⟨G,hG,hsub,hl,hjet⟩ := prep (min ε 1) (lt_min hε zero_lt_one) (min_le_right _ _)
    exact ⟨G,hG,hsub,hl.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hL) hW)),hjet⟩
  · intro q hq hq₁ hqS
    obtain ⟨G,hG,hsub,hl,hjet⟩ := prep (q/2) (by positivity) (by linarith)
    let e : ℝ := q/2*(x1-x0)*(y1-y0)
    have he : 0≤e := by dsimp [e]; positivity
    have hrect := rect_volume (y0:=y0) (y1:=y1) hx
    have hsum : volume S = volume (S\G)+volume G := by
      have hu : (S\G) ∪ G = S := by
        ext z
        constructor
        · rintro (hz|hz)
          · exact hz.1
          · exact hsub hz
        · intro hz
          by_cases hg : z∈G
          · exact Or.inr hg
          · exact Or.inl ⟨hz,hg⟩
      rw [← measure_union disjoint_sdiff_left hG,hu]
    have hqadd : ENNReal.ofReal e + ENNReal.ofReal e ≤ volume S := by
      rw [hrect,← ENNReal.ofReal_mul hq.le] at hqS
      rw [← ENNReal.ofReal_add he he]
      convert hqS using 1
      dsimp [e]
      ring
    have harea : ENNReal.ofReal e ≤ volume G := by
      apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
      exact hqadd.trans (hsum.trans_le (add_le_add_right hl _))
    have hqPow : q^(max 1 (4*N)) ≤ q := by
      conv_rhs => rw [← pow_one q]
      exact pow_le_pow_of_le_one hq.le hq₁ (le_max_left _ _)
    refine ⟨G,hG,hsub,(ENNReal.ofReal_le_ofReal ?_).trans harea,?_⟩
    · dsimp [e]
      calc
        _ ≤ (1/2)*q*(x1-x0)*(y1-y0) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqPow (by norm_num)) hL) hW
        _ = _ := by ring
    · intro p hp i a b hab
      apply (hjet p hp i a b hab).trans
      have hinv : (1:ℝ) ≤ 1/q := (one_le_div hq).2 hq₁
      have hη : 1/(q/2) = 2*(1/q) := by ring
      rw [hη,mul_pow,← mul_assoc D]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv (le_max_right _ _))
            (mul_nonneg hD (by positivity))) (hA i)) (by positivity)

end PaperI.GoodStrips
