import PaperILean.GraphMonotonicityDefinability
import PaperILean.PublishedRealAlgebraicAssumptions
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

/-- Only the graph near the differentiation point is needed. This excludes the
vacuous partial-graph obstruction without requiring a global extension. -/
theorem graphDerivativeRelation_realize_iff_of_local_graph {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (x m : ℝ)
    (hG : ∀ᶠ t in 𝓝 x, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim p ![x,m] ∈ graphDerivativeRelation G ↔ HasDerivAt f m x := by
  obtain ⟨η,hη,hlocal⟩ := Metric.eventually_nhds_iff.mp hG
  have hxG := hlocal (y := x) (by simpa only [dist_self] using hη)
  have hnear {t r : ℝ} (hr : 0 < r) (ht : (t-x)^2 < r^2) : dist t x < r := by
    rw [Real.dist_eq]
    exact (sq_lt_sq₀ (abs_nonneg (t-x)) hr.le).mp (by simpa only [sq_abs] using ht)
  rw [hasDerivAt_iff_polynomial_remainder]
  constructor
  · rintro ⟨z,hz,h⟩ ε hε
    have hz' : z () = f x := (hxG (z ())).mp hz
    obtain ⟨δ,hδ,hbound⟩ := h (fun _ => ε) hε
    refine ⟨min (δ ()) η, lt_min hδ hη, fun t ht => ?_⟩
    have htnear := hnear (lt_min hδ hη) ht
    have htδ : (t-x)^2 < (δ ())^2 := by
      have hdist := htnear.trans_le (min_le_left (δ ()) η)
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (t-x)) hδ.le).mpr
        (by simpa only [Real.dist_eq] using hdist)
    have hrep := hlocal (htnear.trans_le (min_le_right (δ ()) η))
    have hb := hbound ![t,f t] htδ ((hrep (f t)).mpr rfl)
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, hz'] using hb
  · intro h
    refine ⟨fun _ => f x, (hxG (f x)).mpr rfl, ?_⟩
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := h (ε ()) hε
    refine ⟨fun _ => min δ η, lt_min hδ hη, fun q hq hqG => ?_⟩
    have htnear := hnear (lt_min hδ hη) hq
    have htδ : (q 0-x)^2 < δ^2 := by
      have hdist := htnear.trans_le (min_le_left δ η)
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (q 0-x)) hδ.le).mpr
        (by simpa only [Real.dist_eq] using hdist)
    have hrep := hlocal (htnear.trans_le (min_le_right δ η))
    have hq' : q = ![q 0,q 1] := by ext i; fin_cases i <;> rfl
    have hy : q 1 = f (q 0) := (hrep (q 1)).mp (by simpa only [← hq'] using hqG)
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, hy] using hbound (q 0) htδ

theorem graphDerivativeRelation_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x m : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p ![x,m] ∈ graphDerivativeRelation G ↔ HasDerivAt f m x := by
  apply graphDerivativeRelation_realize_iff_of_local_graph
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
  exact hG t ⟨ht.1.le, ht.2.le⟩

theorem realPolynomial_lt_definable {α : Type*} [Finite α]
    (p q : MvPolynomial α ℝ) :
    (univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | MvPolynomial.eval v p < MvPolynomial.eval v q} := by
  simpa only [Set.compl_setOf, not_le] using (realPolynomial_le_definable q p).compl

theorem graphDerivativeRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphDerivativeRelation G) := by
  let B := α ⊕ Fin 2
  let Z := B ⊕ Unit
  let E := Z ⊕ Unit
  let D := E ⊕ Unit
  let Q := D ⊕ Fin 2
  let xi : Q := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))
  let mi : Q := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 1))))
  let zi : Q := Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))
  let ei : Q := Sum.inl (Sum.inl (Sum.inr ()))
  let di : Q := Sum.inl (Sum.inr ())
  let ti : Q := Sum.inr 0
  let yi : Q := Sum.inr 1
  let eQ : (α ⊕ Fin 2) → Q := Sum.elim
    (fun a => Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl a))))) Sum.inr
  let eZ : (α ⊕ Fin 2) → Z := Sum.elim
    (fun a => Sum.inl (Sum.inl a))
    (fun i => if i = 0 then Sum.inl (Sum.inr 0) else Sum.inr ())
  have hWin := realPolynomial_lt_definable
    ((MvPolynomial.X ti - MvPolynomial.X xi)^2) (MvPolynomial.X di ^ 2)
  have hErr := realPolynomial_le_definable
    ((MvPolynomial.X yi - MvPolynomial.X zi -
      MvPolynomial.X mi * (MvPolynomial.X ti - MvPolynomial.X xi))^2)
    (MvPolynomial.X ei ^ 2 * (MvPolynomial.X ti - MvPolynomial.X xi)^2)
  have hAll := realDefinable_forall ((hWin.inter (hG.preimage_comp eQ)).compl.union hErr)
  have hDel := realPolynomial_lt_definable (0 : MvPolynomial D ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have hExD := realDefinable_exists (hDel.inter hAll)
  have hEps := realPolynomial_lt_definable (0 : MvPolynomial E ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have hAllE := realDefinable_forall (hEps.compl.union hExD)
  have hExZ := realDefinable_exists ((hG.preimage_comp eZ).inter hAllE)
  convert hExZ using 1
  ext v
  have heZ (z : Unit → ℝ) : (Sum.elim v z ∘ eZ) =
      Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0),z ()] := by
    funext a
    rcases a with a | i
    · rfl
    · fin_cases i <;> rfl
  have heQ (z ε δ : Unit → ℝ) (q : Fin 2 → ℝ) :
      (Sum.elim (Sum.elim (Sum.elim (Sum.elim v z) ε) δ) q ∘ eQ) =
        Sum.elim (v ∘ Sum.inl) q := by
    funext a
    rcases a with a | i <;> rfl
  simp only [graphDerivativeRelation, mem_setOf_eq, mem_inter_iff, mem_union,
    mem_compl_iff, mem_preimage, MvPolynomial.eval_X, map_zero, map_sub,
    map_pow, map_mul, heZ, heQ, xi, mi, zi, ei, di, ti, yi,
    Sum.elim_inl, Sum.elim_inr]
  change _ ↔ ∃ z : Unit → ℝ, (Sum.elim v z ∘ eZ) ∈ G ∧
    ∀ ε : Unit → ℝ, ¬ (0 < ε ()) ∨ ∃ δ : Unit → ℝ, 0 < δ () ∧
      ∀ q : Fin 2 → ℝ,
        ¬ ((q 0 - v (Sum.inr 0))^2 < (δ ())^2 ∧
          (Sum.elim (Sum.elim (Sum.elim (Sum.elim v z) ε) δ) q ∘ eQ) ∈ G) ∨
        (q 1 - z () - v (Sum.inr 1) * (q 0 - v (Sum.inr 0)))^2 ≤
          (ε ())^2 * (q 0 - v (Sum.inr 0))^2
  simp only [heZ, heQ]
  apply exists_congr
  intro z
  apply and_congr_right
  intro _
  apply forall_congr'
  intro ε
  rw [or_iff_not_imp_left, not_not]
  apply imp_congr_right
  intro _
  apply exists_congr
  intro δ
  apply and_congr_right
  intro _
  apply forall_congr'
  intro q
  tauto

theorem published_graphDerivativeRelation_sign_description {α : Type} [Finite α]
    (hQE : PublishedRealSemialgebraicity) {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    HasPolynomialSignDescription (graphDerivativeRelation G) :=
  hQE.finite_sign_description _ (graphDerivativeRelation_definable hG)

end PaperI
