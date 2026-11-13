import PaperILean.GraphDerivativeLoci
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Fixed-order derivative graphs and their signed superlevels, using actual
local derivatives. The graph may be arbitrary off the represented open interval.
Threshold, sign and interval endpoints are parameters, not fixed constants.
Pre-strategy obstruction record: checkpoint_127_derivative_family_review.md. -/

noncomputable section
namespace PaperI
open Set Filter FirstOrder
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def iteratedGraphDerivativeRelation {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) : ℕ → Set ((α ⊕ Fin 2) → ℝ)
  | 0 => G
  | n + 1 => graphDerivativeRelation (iteratedGraphDerivativeRelation G n)

theorem iteratedGraphDerivativeRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) (n : ℕ) :
    (univ : Set ℝ).Definable Language.ring (iteratedGraphDerivativeRelation G n) := by
  induction n with
  | zero => exact hG
  | succ n ih => exact graphDerivativeRelation_definable ih

/-- Finite-order smoothness on an open interval supplies genuine derivatives
of every preceding order, independent of all behavior outside the interval. -/
theorem differentiableAt_iteratedDeriv_of_contDiffOn_Ioo
    {f : ℝ → ℝ} {a b x : ℝ} {N k : ℕ}
    (hf : ContDiffOn ℝ N f (Ioo a b)) (hk : k < N) (hx : x ∈ Ioo a b) :
    DifferentiableAt ℝ (iteratedDeriv k f) x := by
  have hfx := hf.contDiffAt (Ioo_mem_nhds hx.1 hx.2)
  have hc : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k f) x :=
    hfx.iteratedFDeriv_right (by exact_mod_cast (show 1 + k ≤ N by omega))
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.differentiableAt.comp x
    (hc.differentiableAt (by norm_num))

theorem iteratedGraphDerivativeRelation_realize_iff_on_Ioo {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ)
    (a b : ℝ) (N : ℕ)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hf : ContDiffOn ℝ N f (Ioo a b)) :
    ∀ n ≤ N, ∀ x ∈ Ioo a b, ∀ y : ℝ,
      Sum.elim p ![x,y] ∈ iteratedGraphDerivativeRelation G n ↔
        y = iteratedDeriv n f x := by
  intro n
  induction n with
  | zero => intro _ x hx y; simpa [iteratedGraphDerivativeRelation] using hG x hx y
  | succ n ih =>
    intro hn x hx y
    have hlocal : ∀ᶠ t in 𝓝 x, ∀ z : ℝ,
        Sum.elim p ![t,z] ∈ iteratedGraphDerivativeRelation G n ↔
          z = iteratedDeriv n f t := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      exact ih (Nat.le_trans (Nat.le_succ n) hn) t ht
    rw [iteratedGraphDerivativeRelation,
      graphDerivativeRelation_realize_iff_of_local_graph _ p _ x y hlocal]
    have hd := differentiableAt_iteratedDeriv_of_contDiffOn_Ioo hf
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn) hx
    rw [iteratedDeriv_succ]
    constructor
    · intro hy; exact hy.deriv.symm
    · intro hy; rw [hy]; exact hd.hasDerivAt

/-- Parameters after the original graph parameters are a,b,threshold,sign. -/
def iteratedDerivativeSuperlevelRelation {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (n : ℕ) :
    Set (((α ⊕ Fin 4) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr 0))) (v (Sum.inl (Sum.inr 1))) ∧
    ∃ y : Unit → ℝ,
      Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr ()),y ()] ∈
        iteratedGraphDerivativeRelation G n ∧
      v (Sum.inl (Sum.inr 2)) < v (Sum.inl (Sum.inr 3)) * y ()}

def signedIteratedDerivativeSuperlevel (f : ℝ → ℝ) (n : ℕ) (a b threshold sign : ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ threshold < sign * iteratedDeriv n f x}

theorem iteratedDerivativeSuperlevelRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) (n : ℕ) :
    (univ : Set ℝ).Definable Language.ring (iteratedDerivativeSuperlevelRelation G n) := by
  let e : α ⊕ Fin 2 → ((α ⊕ Fin 4) ⊕ Unit) ⊕ Unit := Sum.elim
    (fun c => Sum.inl (Sum.inl (Sum.inl c)))
    (fun i => if i = 0 then Sum.inl (Sum.inr ()) else Sum.inr ())
  have hineq := realPolynomial_lt_definable
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 2))) :
      MvPolynomial (((α ⊕ Fin 4) ⊕ Unit) ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 3))) * MvPolynomial.X (Sum.inr ()))
  have hvalue := realDefinable_exists
    (((iteratedGraphDerivativeRelation_definable hG n).preimage_comp e).inter hineq)
  have h := ((realCoordinate_lt_definable (Sum.inl (Sum.inr 0)) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr 1)))).inter hvalue
  convert h using 1
  ext v
  have he (y : Unit → ℝ) : Sum.elim v y ∘ e =
      Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr ()),y ()] := by
    funext z
    rcases z with z | i
    · rfl
    · fin_cases i <;> rfl
  simp only [iteratedDerivativeSuperlevelRelation, mem_setOf_eq, mem_inter_iff,
    mem_Ioo, mem_preimage, he, MvPolynomial.eval_X, map_mul, Sum.elim_inl, Sum.elim_inr]

theorem iteratedDerivativeSuperlevelRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ)
    (a b threshold sign : ℝ) (N n : ℕ)
    (hG : ∀ t ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hf : ContDiffOn ℝ N f (Ioo a b)) (hn : n ≤ N) (x : ℝ) :
    Sum.elim (Sum.elim p ![a,b,threshold,sign]) (fun _ => x) ∈
      iteratedDerivativeSuperlevelRelation G n ↔
        x ∈ signedIteratedDerivativeSuperlevel f n a b threshold sign := by
  change (x ∈ Ioo a b ∧ ∃ y : Unit → ℝ, _ ∧ threshold < sign * y ()) ↔
    (x ∈ Ioo a b ∧ threshold < sign * iteratedDeriv n f x)
  apply and_congr_right
  intro hx
  constructor
  · rintro ⟨y,hy,h⟩
    have hy' := (iteratedGraphDerivativeRelation_realize_iff_on_Ioo
      G p f a b N hG hf n hn x hx (y ())).mp hy
    simpa only [hy'] using h
  · intro h
    exact ⟨fun _ => iteratedDeriv n f x,
      (iteratedGraphDerivativeRelation_realize_iff_on_Ioo G p f a b N hG hf n hn x hx _).mpr rfl,h⟩

theorem signedIteratedDerivativeSuperlevel_eq_empty_of_le
    (f : ℝ → ℝ) (n : ℕ) {a b : ℝ} (hab : b ≤ a) (threshold sign : ℝ) :
    signedIteratedDerivativeSuperlevel f n a b threshold sign = ∅ := by
  ext x
  simp only [signedIteratedDerivativeSuperlevel, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hx,_⟩
  exact (not_lt_of_ge hab) (hx.1.trans hx.2)

/-- The highest retained derivative is continuous on the represented open
interval; no smooth extension outside it is used. -/
theorem continuousOn_iteratedDeriv_of_contDiffOn_Ioo
    {f : ℝ → ℝ} {a b : ℝ} {N n : ℕ}
    (hf : ContDiffOn ℝ N f (Ioo a b)) (hn : n ≤ N) :
    ContinuousOn (iteratedDeriv n f) (Ioo a b) := by
  intro x hx
  have hfx := hf.contDiffAt (Ioo_mem_nhds hx.1 hx.2)
  have hc : ContDiffAt ℝ 0 (iteratedFDeriv ℝ n f) x :=
    hfx.iteratedFDeriv_right (by exact_mod_cast (show 0 + n ≤ N by omega))
  rw [iteratedDeriv_eq_equiv_comp]
  exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm.continuousAt.comp
    hc.continuousAt).continuousWithinAt

theorem isOpen_signedIteratedDerivativeSuperlevel
    {f : ℝ → ℝ} {a b : ℝ} {N n : ℕ}
    (hf : ContDiffOn ℝ N f (Ioo a b)) (hn : n ≤ N) (threshold sign : ℝ) :
    IsOpen (signedIteratedDerivativeSuperlevel f n a b threshold sign) := by
  have hc := continuousOn_iteratedDeriv_of_contDiffOn_Ioo hf hn
  exact (continuousOn_const.mul hc).isOpen_inter_preimage isOpen_Ioo isOpen_Ioi

end PaperI
