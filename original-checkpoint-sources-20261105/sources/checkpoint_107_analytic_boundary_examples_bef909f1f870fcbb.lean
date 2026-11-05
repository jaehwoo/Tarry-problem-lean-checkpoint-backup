import PaperILean.DerivativeSignSubdivision
import PaperILean.GraphDerivativeDefinability
import PaperILean.SemialgebraicPathAnalyticity

open Set
open PaperI

-- Post-implementation boundary checks. These do not replace the recorded
-- pre-strategy diagnostics and are not included in the claimed theorem count.

example (m : ℝ) :
    Sum.elim (fun _ : Unit => (0 : ℝ)) ![0,m] ∈
      graphDerivativeRelation {v : (Unit ⊕ Fin 2) → ℝ |
        v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0} := by
  refine ⟨fun _ => 0, by simp, ?_⟩
  intro ε _
  refine ⟨fun _ => 1, zero_lt_one, ?_⟩
  intro q _ hq
  change q 0 = 0 ∧ q 1 = 0 at hq
  simp [hq.1,hq.2]

example : ¬ HasDerivAt (fun t : ℝ => t) 2 0 := by
  intro h
  have hh := h.unique (hasDerivAt_id 0)
  norm_num at hh

example (c a b : ℝ) :
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, (fun _ : ℝ => c) x = (fun _ : ℝ => c) y := by
  exact constantOn_of_zero_derivative (differentiableOn_const c) (by simp)

example (f : ℝ → ℝ) (a : ℝ) : DerivativeSignOn f (Ioo a a) := by
  left
  simp

example (f : ℝ → ℝ) {a b : ℝ} (hab : b ≤ a) :
    MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b) := by
  left
  intro x hx
  exact ((not_lt_of_ge hab) (hx.1.trans hx.2)).elim
