import PaperILean.PublishedRawFormulaConditioning
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
noncomputable section
open scoped Topology
open Set Filter

-- Nonzero derivatives on selected regular points do not imply global injectivity.
example (x : ℝ) : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> simp
example (x : ℝ) (hx : x ≠ 0) : 2*x ≠ 0 := mul_ne_zero (by norm_num) hx
example : ¬ Set.InjOn (fun x : ℝ => x^2) {x | x ≠ 0} := by
  intro h
  have he := h (show (1:ℝ) ≠ 0 by norm_num) (show (-1:ℝ) ≠ 0 by norm_num)
    (show (1:ℝ)^2=(-1)^2 by norm_num)
  norm_num at he

-- Rectangular rank/nonzero derivative is not the square invertible derivative condition.
example (y : ℝ) : Set.Infinite {x : ℝ × ℝ | x.1 = y} := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℝ => (y,t))
  · intro a b h
    exact congrArg Prod.snd h
  · intro t
    rfl

-- A derivative within a singleton can be assigned arbitrarily; use actual ambient
-- derivatives (or the ambient open-set derivative) at every selected point.
example : HasFDerivWithinAt (fun _ : ℝ => (0:ℝ))
    (ContinuousLinearMap.id ℝ ℝ) ({0} : Set ℝ) 0 := by
  apply HasFDerivWithinAt.of_not_accPt
  simp [accPt_principal_iff_nhdsWithin]

-- Selected domains need not be open; their boundary is retained in the fiber.
example : {x : ℝ | x ∈ Set.Icc 0 1 ∧ (fun y : ℝ => y) x = 0} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.2
  · intro h
    subst x
    norm_num
example (f : ℝ → ℝ) (y : ℝ) : {x : ℝ | x ∈ (∅ : Set ℝ) ∧ f x = y} = ∅ := by simp

-- Discreteness alone does not give finite fibers: uniform semialgebraic component
-- control is an independent input, and Nat.card is unsafe before proving Finite.
example : DiscreteTopology ℤ := inferInstance
example : Infinite ℤ := inferInstance
example : Nat.card ℤ = 0 := Nat.card_eq_zero_of_infinite

-- No real coefficient magnitude restriction is part of invertibility.
example (a : ℝ) (ha : a ≠ 0) : Function.Injective (fun x : ℝ => a*x) := by
  intro x y h
  exact mul_left_cancel₀ ha h
