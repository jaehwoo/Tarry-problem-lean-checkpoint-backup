import PaperILean.RealPolynomialDefinability
import Mathlib.Algebra.MvPolynomial.Degrees

/-! A checked compiler from actual mathlib ring terms to real polynomials.
The ring language has integer literals via 0,1,+,-,*; arbitrary real named
constants are retained as separately valued free variables, as in mathlib's
`definable_iff_exists_formula_sum`. No named real is rounded or discarded.
The degree bound is syntactic and therefore independent of every valuation.
Executed pre-strategy cases: checkpoint_105_ring_compiler_pre_strategy.json. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Evaluate the original term in the polynomial ring, assigning X_i to its
exact variable i. No variable, including a bound-coordinate label, is renamed. -/
def ringTermPolynomial {α : Type*} (t : Language.ring.Term α) : MvPolynomial α ℝ :=
  t.realize MvPolynomial.X

/-- A syntax-only degree bound; cancellation can make the actual degree smaller. -/
def ringTermDegreeBound {α : Type*} : Language.ring.Term α → ℕ
  | .var _ => 1
  | .func .add ts => max (ringTermDegreeBound (ts 0)) (ringTermDegreeBound (ts 1))
  | .func .mul ts => ringTermDegreeBound (ts 0) + ringTermDegreeBound (ts 1)
  | .func .neg ts => ringTermDegreeBound (ts 0)
  | .func .zero _ => 0
  | .func .one _ => 0

/-- Polynomial evaluation is exactly the original raw-term realization. -/
theorem ringTermPolynomial_eval {α : Type*} (t : Language.ring.Term α)
    (x : α → ℝ) : MvPolynomial.eval x (ringTermPolynomial t) = t.realize x := by
  induction t with
  | var i => simp [ringTermPolynomial, Language.Term.realize]
  | func f ts ih =>
    cases f <;> simp [ringTermPolynomial, Language.Term.realize,
      FirstOrder.Ring.CompatibleRing.funMap_add,
      FirstOrder.Ring.CompatibleRing.funMap_mul,
      FirstOrder.Ring.CompatibleRing.funMap_neg,
      FirstOrder.Ring.CompatibleRing.funMap_zero,
      FirstOrder.Ring.CompatibleRing.funMap_one] at * <;> simp [ih]

/-- The bound depends on the original syntax, before any real assignment. -/
theorem ringTermPolynomial_totalDegree_le {α : Type*} (t : Language.ring.Term α) :
    (ringTermPolynomial t).totalDegree ≤ ringTermDegreeBound t := by
  induction t with
  | var i => simp [ringTermPolynomial, Language.Term.realize, ringTermDegreeBound]
  | func f ts ih =>
    cases f with
    | add =>
      exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max (ih 0) (ih 1))
    | mul =>
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (ih 0) (ih 1))
    | neg => simpa [ringTermPolynomial, Language.Term.realize, ringTermDegreeBound] using ih 0
    | zero => simp [ringTermPolynomial, Language.Term.realize, ringTermDegreeBound]
    | one => simp [ringTermPolynomial, Language.Term.realize, ringTermDegreeBound]

/-- Equality atoms become the zero locus of the exact difference polynomial. -/
theorem ringTermPolynomial_sub_eq_zero_iff {α : Type*}
    (t u : Language.ring.Term α) (x : α → ℝ) :
    MvPolynomial.eval x (ringTermPolynomial t - ringTermPolynomial u) = 0 ↔
      t.realize x = u.realize x := by
  rw [map_sub, ringTermPolynomial_eval, ringTermPolynomial_eval, sub_eq_zero]

/-- The equality-atom degree is bounded before all variable and parameter values. -/
theorem ringTermPolynomial_sub_totalDegree_le {α : Type*}
    (t u : Language.ring.Term α) :
    (ringTermPolynomial t - ringTermPolynomial u).totalDegree ≤
      max (ringTermDegreeBound t) (ringTermDegreeBound u) :=
  (MvPolynomial.totalDegree_sub _ _).trans
    (max_le_max (ringTermPolynomial_totalDegree_le t) (ringTermPolynomial_totalDegree_le u))

end PaperI
