import PaperILean.DefinableDistanceBands
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! I1259/I1265: Borel Euclidean diameter of jointly semialgebraic bounded
fibers. A diameter is a supremum, not an attained maximum. The real-QE input
is explicit; neither Borel projection nor compactness of open fibers is assumed. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarFiberDiameter {ρ : Type*} (H : Set ((ρ ⊕ Fin 2) → ℝ))
    (p : ρ → ℝ) : ℝ :=
  Metric.diam ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p)

theorem planarFiberDiameter_nonneg {ρ : Type*} (H : Set ((ρ ⊕ Fin 2) → ℝ))
    (p : ρ → ℝ) : 0 ≤ planarFiberDiameter H p := Metric.diam_nonneg

theorem planarFiberDiameter_empty {ρ : Type*} {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    {p : ρ → ℝ} (h : projectionFiber H p = ∅) : planarFiberDiameter H p = 0 := by
  simp [planarFiberDiameter,h]

theorem planarFiberDiameter_singleton {ρ : Type*} {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    {p : ρ → ℝ} {x : Fin 2 → ℝ} (h : projectionFiber H p = {x}) :
    planarFiberDiameter H p = 0 := by
  simp [planarFiberDiameter,h]

theorem planarFiberDiameter_le_iff {ρ : Type*} (H : Set ((ρ ⊕ Fin 2) → ℝ))
    (p : ρ → ℝ)
    (hb : Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p)) (r : ℝ) :
    planarFiberDiameter H p ≤ r ↔ 0 ≤ r ∧
      ∀ x ∈ projectionFiber H p, ∀ y ∈ projectionFiber H p,
        planarSquaredDist x y ≤ r^2 := by
  constructor
  · intro h
    refine ⟨(planarFiberDiameter_nonneg H p).trans h,?_⟩
    intro x hx y hy
    rw [planarSquaredDist_eq_dist_sq]
    exact pow_le_pow_left₀ dist_nonneg
      ((Metric.dist_le_diam_of_mem hb ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩).trans h) 2
  · rintro ⟨hr,h⟩
    apply Metric.diam_le_of_forall_dist_le hr
    rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩
    have hxy := h x hx y hy
    rw [planarSquaredDist_eq_dist_sq] at hxy
    nlinarith [dist_nonneg (x := (WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
      (y := (WithLp.equiv 2 (Fin 2 → ℝ)).symm y)]

theorem planarFiberPairwiseBound_definable {ρ : Type*} [Finite ρ]
    {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hH : (univ : Set ℝ).Definable Language.ring H) (r : ℝ) :
    (univ : Set ℝ).Definable Language.ring
      {p : ρ → ℝ | ∀ x ∈ projectionFiber H p, ∀ y ∈ projectionFiber H p,
        planarSquaredDist x y ≤ r^2} := by
  let a : ρ ⊕ Fin 2 → (ρ ⊕ Fin 2) ⊕ Fin 2 := Sum.inl
  let b : ρ ⊕ Fin 2 → (ρ ⊕ Fin 2) ⊕ Fin 2 :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  let q : MvPolynomial ((ρ ⊕ Fin 2) ⊕ Fin 2) ℝ :=
    planarSquaredDistPolynomial (fun i : Fin 2 => Sum.inl (Sum.inr i)) Sum.inr
  have h := realDefinable_forall (realDefinable_forall
    (((hH.preimage_comp a).inter (hH.preimage_comp b)).compl.union
      (realPolynomial_le_definable q (MvPolynomial.C (r^2)))))
  convert h using 1
  ext p
  have ha (x y : Fin 2 → ℝ) : Sum.elim (Sum.elim p x) y ∘ a = Sum.elim p x := rfl
  have hb (x y : Fin 2 → ℝ) : Sum.elim (Sum.elim p x) y ∘ b = Sum.elim p y := by
    funext i; cases i <;> rfl
  simp only [mem_setOf_eq,mem_preimage,mem_union,mem_compl_iff,mem_inter_iff,
    ha,hb,q,planarSquaredDistPolynomial_eval,MvPolynomial.eval_C,
    Function.comp_def,Sum.elim_inl,Sum.elim_inr,projectionFiber]
  simp only [Function.comp_def] at ha hb
  simp only [ha,hb]
  constructor
  · intro hv x y
    by_cases hxy : Sum.elim p x ∈ H ∧ Sum.elim p y ∈ H
    · exact Or.inr (hv x hxy.1 y hxy.2)
    · exact Or.inl hxy
  · intro hv x hx y hy
    rcases hv x y with hbad | hgood
    · exact (hbad ⟨hx,hy⟩).elim
    · exact hgood

theorem published_planarFiberDiameter_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {H : Set ((ρ ⊕ Fin 2) → ℝ)} (hH : HasPolynomialSignDescription H)
    (hb : ∀ p : ρ → ℝ, Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p)) :
    Measurable (planarFiberDiameter H) := by
  apply measurable_of_Iic
  intro r
  by_cases hr : 0 ≤ r
  · have hs := hQE.finite_sign_description _
      (planarFiberPairwiseBound_definable (hasPolynomialSignDescription_definable hH) r)
    have hm : MeasurableSet {p : ρ → ℝ |
        ∀ x ∈ projectionFiber H p, ∀ y ∈ projectionFiber H p,
          planarSquaredDist x y ≤ r^2} := by
      simpa only [← BorelSpace.measurable_eq] using hasPolynomialSignDescription_borel hs
    convert hm using 1
    ext p
    simp only [mem_preimage,mem_Iic,mem_setOf_eq,planarFiberDiameter_le_iff H p (hb p) r,hr,true_and]
  · have he : planarFiberDiameter H ⁻¹' Iic r = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro p hp
      exact hr ((planarFiberDiameter_nonneg H p).trans hp)
    rw [he]
    exact MeasurableSet.empty

end PaperI
