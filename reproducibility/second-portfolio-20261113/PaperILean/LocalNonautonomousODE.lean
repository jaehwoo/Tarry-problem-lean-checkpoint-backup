import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue

/-! Local nonautonomous ODE existence by adjoining the actual time variable.
No global interval of existence is inferred from the local theorem. -/
noncomputable section
open Set
open scoped ContDiff
namespace PaperI

theorem exists_local_nonautonomous_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E)
    (hv : ContDiffAt ℝ 1 (fun p : ℝ × E => v p.1 p.2) (t₀, x₀)) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (v t (f t)) t := by
  have ha : ContDiffAt ℝ 1 (fun p : ℝ × E => ((1 : ℝ), v p.1 p.2)) (t₀, x₀) :=
    contDiffAt_const.prodMk hv
  obtain ⟨g, hg0, ε, hε, hg⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀ ha
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hfst : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun s => (g s).1) 1 t := by
    intro t ht
    exact (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t (hg t ht)
  have hc : EqOn (fun t => (g t).1) (fun t => t) (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun t ht => (hfst t ht).differentiableAt.differentiableWithinAt)
      differentiableOn_id
    · intro t ht
      exact ((hfst t ht).deriv).trans (hasDerivAt_id t).deriv.symm
    · exact ht₀
    · exact congrArg Prod.fst hg0
  refine ⟨fun t => (g t).2, congrArg Prod.snd hg0, ε, hε, ?_⟩
  intro t ht
  have hd := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t (hg t ht)
  change HasDerivAt (fun s => (g s).2) (v (g t).1 (g t).2) t at hd
  simpa only [hc ht] using hd

theorem contDiffOn_of_smooth_vectorField {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : ℝ × E → E} {f : ℝ → E} {s : Set ℝ}
    (hs : IsOpen s) (hf : ∀ t ∈ s, HasDerivAt f (v (t, f t)) t)
    (hv : ∀ t ∈ s, ContDiffAt ℝ ∞ v (t, f t)) : ContDiffOn ℝ ∞ f s := by
  have hd : DifferentiableOn ℝ f s := fun t ht => (hf t ht).differentiableAt.differentiableWithinAt
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hd.continuousOn
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
      refine ⟨hd, by simp, ?_⟩
      have he : EqOn (deriv f) (fun t => v (t, f t)) s := fun t ht => (hf t ht).deriv
      apply ContDiffOn.congr _ he
      intro t ht
      exact (((hv t ht).of_le (m := (n : WithTop ℕ∞))
        (WithTop.coe_le_coe.mpr le_top)).comp t
        (contDiffAt_id.prodMk (ih.contDiffAt (hs.mem_nhds ht)))).contDiffWithinAt

end PaperI
