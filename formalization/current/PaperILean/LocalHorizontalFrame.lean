import PaperILean.HorizontalFrameAlgebra
import PaperILean.LocalNonautonomousODE
import PaperILean.SmoothMinimizingGram

/-! I292: an actual smooth local horizontal lift, with prescribed initial frame.
The interval radius is local and may depend on the path and the initial frame.
This module does not assert continuation to the whole source interval [0,1]. -/
noncomputable section
open Set Filter
open scoped Matrix Matrix.L2OpNorm Topology ContDiff
namespace PaperI

theorem contDiffAt_horizontalFrameField (Q : ℝ → SymmetricMatrix 3)
    (t : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : ContDiffAt ℝ ∞ (deriv Q) t) (hB : IsUnit B) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
      horizontalFrameVelocity (deriv Q p.1).val p.2) (t, B) := by
  have hd : ContDiffAt ℝ ∞ (fun p : ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
      (deriv Q p.1).val) (t, B) :=
    ((symmetricMatrixIncl 3).contDiff.contDiffAt.of_le (m := ∞) le_top).comp (t, B)
      (hQ.comp (t, B) contDiffAt_fst)
  exact ContDiffAt.comp
    (f := fun p : ℝ × Matrix (Fin 3) (Fin 3) ℝ => ((deriv Q p.1).val, p.2))
    (g := fun p : Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ =>
      horizontalFrameVelocity p.1 p.2) (t, B)
    ((contDiffAt_horizontalFrameVelocity (deriv Q t).val B hB).of_le (m := ∞) le_top)
    (hd.prodMk contDiffAt_snd)

theorem exists_local_horizontalFrame (Q : ℝ → SymmetricMatrix 3) {s : Set ℝ}
    (hs : IsOpen s) (hQ : ContDiffOn ℝ ∞ Q s) (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (B₀ : PositiveFrame) (hGram : B₀.val * B₀.valᵀ = (Q t₀).val) :
    ∃ ε > (0 : ℝ), ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      B t₀ = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), t ∈ s ∧ 0 < (B t).det ∧
        B t * (B t)ᵀ = (Q t).val ∧
        (horizontalFrameGenerator (deriv Q t).val (B t)).IsSymm ∧
        HasDerivAt B (B t * horizontalFrameGenerator (deriv Q t).val (B t)) t := by
  have hdQ : ContDiffOn ℝ ∞ (deriv Q) s :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hs).mp hQ).2
  have hfield := contDiffAt_horizontalFrameField Q t₀ B₀.val
    (hdQ.contDiffAt (hs.mem_nhds ht₀)) (positiveFrame_isUnit B₀)
  obtain ⟨B, hB₀, δ, hδ, hB⟩ := exists_local_nonautonomous_solution
    (fun t C => horizontalFrameVelocity (deriv Q t).val C) t₀ B₀.val
      (hfield.of_le (WithTop.coe_le_coe.mpr le_top))
  have hδ₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hc : ContinuousAt B t₀ := (hB t₀ hδ₀).continuousAt
  have hdet : ContinuousAt (fun t => (B t).det) t₀ :=
    contDiff_matrix_det_three.continuous.continuousAt.comp hc
  have hp : 0 < (B t₀).det := by rw [hB₀]; exact B₀.property
  have hn : {t | t ∈ s ∧ t ∈ Ioo (t₀ - δ) (t₀ + δ) ∧ 0 < (B t).det} ∈ 𝓝 t₀ :=
    inter_mem (hs.mem_nhds ht₀) (inter_mem (isOpen_Ioo.mem_nhds hδ₀)
      (hdet.preimage_mem_nhds (Ioi_mem_nhds hp)))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hn
  rw [Real.ball_eq_Ioo] at he
  have hunit : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), IsUnit (B t) := by
    intro t ht
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (he ht).2.2.ne')
  have hode : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt B (horizontalFrameVelocity (deriv Q t).val (B t)) t :=
    fun t ht => hB t (he ht).2.1
  have hsm : ContDiffOn ℝ ∞ B (Ioo (t₀ - ε) (t₀ + ε)) :=
    contDiffOn_of_smooth_vectorField isOpen_Ioo hode (fun t ht =>
      contDiffAt_horizontalFrameField Q t (B t)
        (hdQ.contDiffAt (hs.mem_nhds (he ht).1)) (hunit t ht))
  have hQt : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => (Q u).val) (deriv Q t).val t := by
    intro t ht
    exact (symmetricMatrixIncl 3).hasFDerivAt.comp_hasDerivAt t
      ((hQ.contDiffAt (hs.mem_nhds (he ht).1)).differentiableAt
        (WithTop.coe_le_coe.mpr le_top)).hasDerivAt
  have hg : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => B u * (B u)ᵀ) (deriv Q t).val t :=
    fun t ht => hasDerivAt_frameGram_horizontal (hode t ht) (deriv Q t).property (hunit t ht)
  have heq : EqOn (fun t => B t * (B t)ᵀ) (fun t => (Q t).val)
      (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (x := t₀) (convex_Ioo _ _).isPreconnected
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hQt t ht).differentiableAt.differentiableWithinAt)
    · intro t ht
      exact (hg t ht).deriv.trans (hQt t ht).deriv.symm
    · exact ⟨by linarith, by linarith⟩
    · simpa only [hB₀] using hGram
  refine ⟨ε, hε, B, hB₀, hsm, ?_⟩
  intro t ht
  refine ⟨(he ht).1, (he ht).2.2, heq ht,
    horizontalFrameGenerator_isSymm _ _ (deriv Q t).property, ?_⟩
  simpa only [mul_horizontalFrameGenerator _ _ (hunit t ht)] using hode t ht

theorem exists_local_horizontal_minimizingFrame {k : ℕ} (F : CoefficientSpace k)
    (c : ℝ → PhysicalSpace) {s : Set ℝ} (hs : IsOpen s)
    (hc : ContDiffOn ℝ ∞ c s) (lam : ℝ) (hlam : 0 < lam)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s) (B₀ : PositiveFrame)
    (hmin : ∀ D : PositiveFrame, FrameEnergy F (c t₀) lam B₀.val ≤
      FrameEnergy F (c t₀) lam D.val) :
    ∃ ε > (0 : ℝ), ∃ B : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      B t₀ = B₀.val ∧ ContDiffOn ℝ ∞ B (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), t ∈ s ∧ ∃ hpos : 0 < (B t).det,
        (∀ D : PositiveFrame, FrameEnergy F (c t) lam (B t) ≤ FrameEnergy F (c t) lam D.val) ∧
        ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.IsSymm ∧ HasDerivAt B (B t * S) t := by
  let Q : ℝ → SymmetricMatrix 3 := fun t => minimizingGram lam hlam (F, c t)
  have hQ : ContDiffOn ℝ ∞ Q s :=
    (contDiff_infty_minimizingGram lam hlam).comp_contDiffOn (contDiffOn_const.prodMk hc)
  have hGram : B₀.val * B₀.valᵀ = (Q t₀).val := by
    dsimp only [Q]
    rw [minimizingGram_eq_of_minimum F (c t₀) lam hlam B₀ hmin]
    rfl
  obtain ⟨ε, hε, B, hB₀, hsm, hb⟩ := exists_local_horizontalFrame Q hs hQ t₀ ht₀ B₀ hGram
  refine ⟨ε, hε, B, hB₀, hsm, ?_⟩
  intro t ht
  obtain ⟨hts, hp, hgram, hS, hd⟩ := hb t ht
  refine ⟨hts, hp, ?_, _, hS, hd⟩
  intro D
  have he : FrameEnergy F (c t) lam (B t) =
      FrameEnergy F (c t) lam (minimizingFrame F (c t) lam hlam).val :=
    FrameEnergy_eq_of_same_gram F (c t) lam ⟨B t, hp⟩
      (minimizingFrame F (c t) lam hlam) hgram
  rw [he]
  exact minimizingFrame_is_minimum F (c t) lam hlam D

end PaperI
