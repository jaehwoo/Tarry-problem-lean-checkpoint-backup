import PaperILean.HorizontalFrameContinuation

/-! I292: a smooth horizontal lift on an open interval containing the entire
closed path [0,1], and its application to the actual minimizing Gram. -/
noncomputable section
open Set Filter
open scoped Matrix Matrix.L2OpNorm Topology ContDiff
namespace PaperI

theorem exists_Icc_extension_of_isOpen {s : Set ℝ} (hs : IsOpen s)
    (hi : Icc (0 : ℝ) 1 ⊆ s) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ s := by
  obtain ⟨l₀, u₀, h₀, hs₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hs.mem_nhds (hi ⟨le_rfl, zero_le_one⟩))
  obtain ⟨l₁, u₁, h₁, hs₁⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hs.mem_nhds (hi ⟨zero_le_one, le_rfl⟩))
  refine ⟨l₀ / 2, (1 + u₁) / 2, by linarith [h₀.1], by linarith [h₁.2], ?_⟩
  intro t ht
  rcases lt_or_ge t 0 with ht₀ | ht₀
  · apply hs₀
    exact ⟨by linarith [ht.1, h₀.1], ht₀.trans h₀.2⟩
  · rcases le_or_gt t 1 with ht₁ | ht₁
    · exact hi ⟨ht₀, ht₁⟩
    · apply hs₁
      exact ⟨h₁.1.trans ht₁, by linarith [ht.2, h₁.2]⟩

theorem exists_horizontalFrame_covering_unitInterval (Q : ℝ → SymmetricMatrix 3)
    {s : Set ℝ} (hs : IsOpen s) (hi : Icc (0 : ℝ) 1 ⊆ s)
    (hQ : ContDiffOn ℝ ∞ Q s) (hp : ∀ t ∈ s, (Q t).val.PosDef)
    (B₀ : PositiveFrame) (hGram : B₀.val * B₀.valᵀ = (Q 0).val) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ s ∧
      ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        B 0 = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo a b) ∧
        ∀ t ∈ Ioo a b, 0 < (B t).det ∧ B t * (B t)ᵀ = (Q t).val ∧
          (horizontalFrameGenerator (deriv Q t).val (B t)).IsSymm ∧
          HasDerivAt B (B t * horizontalFrameGenerator (deriv Q t).val (B t)) t := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_Icc_extension_of_isOpen hs hi
  exact ⟨a, b, ha, hb, hab, exists_horizontalFrame_Ioo Q hs hQ hp hab
    ⟨ha, zero_lt_one.trans hb⟩ B₀ hGram⟩

theorem exists_horizontal_minimizingFrame_covering_unitInterval {k : ℕ}
    (F : CoefficientSpace k) (c : ℝ → PhysicalSpace) {s : Set ℝ}
    (hs : IsOpen s) (hi : Icc (0 : ℝ) 1 ⊆ s) (hc : ContDiffOn ℝ ∞ c s)
    (lam : ℝ) (hlam : 0 < lam) (B₀ : PositiveFrame)
    (hmin : ∀ D : PositiveFrame, FrameEnergy F (c 0) lam B₀.val ≤
      FrameEnergy F (c 0) lam D.val) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Icc a b ⊆ s ∧
      ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        B 0 = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo a b) ∧
        ∀ t ∈ Ioo a b, 0 < (B t).det ∧
          (∀ D : PositiveFrame, FrameEnergy F (c t) lam (B t) ≤ FrameEnergy F (c t) lam D.val) ∧
          ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.IsSymm ∧ HasDerivAt B (B t * S) t := by
  let Q : ℝ → SymmetricMatrix 3 := fun t => minimizingGram lam hlam (F, c t)
  have hQ : ContDiffOn ℝ ∞ Q s :=
    (contDiff_infty_minimizingGram lam hlam).comp_contDiffOn (contDiffOn_const.prodMk hc)
  have hp : ∀ t ∈ s, (Q t).val.PosDef := fun t _ => minimizingGram_posDef lam hlam (F, c t)
  have hGram : B₀.val * B₀.valᵀ = (Q 0).val := by
    dsimp only [Q]
    rw [minimizingGram_eq_of_minimum F (c 0) lam hlam B₀ hmin]
    rfl
  obtain ⟨a, b, ha, hb, hab, B, hB₀, hsm, hB⟩ :=
    exists_horizontalFrame_covering_unitInterval Q hs hi hQ hp B₀ hGram
  refine ⟨a, b, ha, hb, hab, B, hB₀, hsm, ?_⟩
  intro t ht
  obtain ⟨hpos, hgram, hsym, hder⟩ := hB t ht
  refine ⟨hpos, ?_, _, hsym, hder⟩
  intro D
  have he : FrameEnergy F (c t) lam (B t) =
      FrameEnergy F (c t) lam (minimizingFrame F (c t) lam hlam).val :=
    FrameEnergy_eq_of_same_gram F (c t) lam ⟨B t, hpos⟩
      (minimizingFrame F (c t) lam hlam) hgram
  rw [he]
  exact minimizingFrame_is_minimum F (c t) lam hlam D

end PaperI

