import PaperILean.GraphMonotonicityDefinability
import PaperILean.PublishedRealQuantifierElimination
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-! Definability of the actual derivative graph by a polynomial epsilon-delta
formula. The realization theorem requires a genuine total graph; a partial
graph with holes does not certify a derivative. The formula itself introduces
no analytic, monotonicity, or quantitative subdivision assumption. -/

noncomputable section
namespace PaperI
open Set Filter Asymptotics FirstOrder
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem hasDerivAt_iff_polynomial_remainder {f : ℝ → ℝ} {m x : ℝ} :
    HasDerivAt f m x ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      (t-x)^2 < δ^2 → (f t-f x-m*(t-x))^2 ≤ ε^2*(t-x)^2 := by
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (h hε)
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have ht' : dist t x < δ := by
      rw [Real.dist_eq]
      exact (sq_lt_sq₀ (abs_nonneg (t-x)) hδ.le).mp (by simpa only [sq_abs] using ht)
    have hb := hbound ht'
    simp only [Real.norm_eq_abs, smul_eq_mul] at hb
    have hs := (sq_le_sq₀ (abs_nonneg (f t-f x-(t-x)*m))
      (mul_nonneg hε.le (abs_nonneg (t-x)))).mpr hb
    simpa only [sq_abs, mul_pow, mul_comm] using hs
  · intro h ε hε
    obtain ⟨δ,hδ,hbound⟩ := h ε hε
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨δ,hδ,fun t ht => ?_⟩
    have ht' : (t-x)^2 < δ^2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (t-x)) hδ.le).mpr
        (by simpa only [Real.dist_eq] using ht)
    have hb := hbound t ht'
    simp only [Real.norm_eq_abs, smul_eq_mul]
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε.le (abs_nonneg _))).mp
    simpa only [sq_abs, mul_pow, mul_comm] using hb

def graphDerivativeRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set ((α ⊕ Fin 2) → ℝ) :=
  {v | ∃ z : Unit → ℝ,
    Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0), z ()] ∈ G ∧
    ∀ ε : Unit → ℝ, 0 < ε () → ∃ δ : Unit → ℝ, 0 < δ () ∧
      ∀ q : Fin 2 → ℝ, (q 0 - v (Sum.inr 0))^2 < (δ ())^2 →
        Sum.elim (v ∘ Sum.inl) q ∈ G →
        (q 1 - z () - v (Sum.inr 1) * (q 0 - v (Sum.inr 0)))^2 ≤
          (ε ())^2 * (q 0 - v (Sum.inr 0))^2}

theorem graphDerivativeRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ)
    (hG : ∀ t y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) (x m : ℝ) :
    Sum.elim p ![x,m] ∈ graphDerivativeRelation G ↔ HasDerivAt f m x := by
  rw [hasDerivAt_iff_polynomial_remainder]
  constructor
  · rintro ⟨z,hz,h⟩ ε hε
    have hz' : z () = f x := (hG x (z ())).mp hz
    obtain ⟨δ,hδ,hbound⟩ := h (fun _ => ε) hε
    refine ⟨δ (),hδ,fun t ht => ?_⟩
    have hb := hbound ![t,f t] ht ((hG t (f t)).mpr rfl)
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, hz'] using hb
  · intro h
    refine ⟨fun _ => f x, (hG x (f x)).mpr rfl, ?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := h (ε ()) hε
    refine ⟨fun _ => δ,hδ,fun q hq hqG => ?_⟩
    have hq' : q = ![q 0,q 1] := by ext i; fin_cases i <;> rfl
    have hy : q 1 = f (q 0) := (hG (q 0) (q 1)).mp (by simpa only [← hq'] using hqG)
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, hy] using hbound (q 0) hq

theorem realPolynomial_lt_definable {α : Type*} [Finite α]
    (p q : MvPolynomial α ℝ) :
    (univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v p < MvPolynomial.eval v q} := by
  simpa only [Set.compl_setOf, not_le] using (realPolynomial_le_definable q p).compl

end PaperI
