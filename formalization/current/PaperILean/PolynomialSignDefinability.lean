import PaperILean.PolynomialSignDescription
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The elementary direction from finite polynomial-sign descriptions to
real-ring definability. A finite collection of realized sign classes describes
the exact set. This is Boolean encoding, not quantifier elimination. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

theorem polynomialSignDetermined_finite_sign_classes {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined A S) :
    ∃ R : Finset (α → ℝ), S = ⋃ r ∈ R,
      {v | ∀ p ∈ A, RealSignEquivalent (MvPolynomial.eval r p) (MvPolynomial.eval v p)} := by
  classical
  let code : (α → ℝ) → (A → Bool × Bool) := fun v p =>
    (decide (MvPolynomial.eval v p.val = 0), decide (0 < MvPolynomial.eval v p.val))
  let I : Set (A → Bool × Bool) := code '' S
  letI : Fintype I := Fintype.ofFinite I
  let rep : I → (α → ℝ) := fun i => Classical.choose i.property
  have hrep (i : I) : rep i ∈ S ∧ code (rep i) = i.val :=
    Classical.choose_spec i.property
  have hcode (x y : α → ℝ) (h : code x = code y) :
      ∀ p ∈ A, RealSignEquivalent (MvPolynomial.eval x p) (MvPolynomial.eval y p) := by
    intro p hp
    have hbits := congrFun h (⟨p, hp⟩ : A)
    exact ⟨decide_eq_decide.mp (congrArg Prod.fst hbits),
      decide_eq_decide.mp (congrArg Prod.snd hbits)⟩
  refine ⟨Finset.univ.image rep, ?_⟩
  ext v
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro hv
    let i : I := ⟨code v, ⟨v, hv, rfl⟩⟩
    refine ⟨rep i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hcode (rep i) v (hrep i).2
  · rintro ⟨r, hr, hrv⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hS (rep i) v hrv).mp (hrep i).1

theorem realSignEquivalent_polynomial_definable {α : Type*} [Finite α]
    (a : ℝ) (p : MvPolynomial α ℝ) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | RealSignEquivalent a (MvPolynomial.eval v p)} := by
  have hz := realPolynomial_zero_definable p
  have hp : (Set.univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | 0 < MvPolynomial.eval v p} := by
    simpa only [Set.compl_setOf, map_neg, not_le, neg_lt_zero] using
      (realPolynomial_nonneg_definable (-p)).compl
  by_cases ha : a = 0 <;> by_cases hb : 0 < a
  · exact False.elim (by simpa [ha] using hb)
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.inter hp.compl
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.compl.inter hp
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.compl.inter hp.compl

theorem polynomialSignDetermined_definable {α : Type*} [Finite α]
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined A S) :
    (Set.univ : Set ℝ).Definable Language.ring S := by
  obtain ⟨R, hR⟩ := polynomialSignDetermined_finite_sign_classes A S hS
  rw [hR]
  apply Set.definable_finset_biUnion
  intro r
  have h := Set.definable_finset_biInter
    (fun p : MvPolynomial α ℝ => realSignEquivalent_polynomial_definable (MvPolynomial.eval r p) p) A
  simpa only [Set.setOf_forall] using h

theorem hasPolynomialSignDescription_definable {α : Type*} [Finite α]
    {S : Set (α → ℝ)} (hS : HasPolynomialSignDescription S) :
    (Set.univ : Set ℝ).Definable Language.ring S := by
  obtain ⟨A, hA⟩ := hS
  exact polynomialSignDetermined_definable A S hA

theorem realSignEquivalent_polynomial_borel {α : Type*}
    (a : ℝ) (p : MvPolynomial α ℝ) :
    @MeasurableSet (α → ℝ) (borel (α → ℝ))
      {v | RealSignEquivalent a (MvPolynomial.eval v p)} := by
  borelize (α → ℝ)
  have hz : MeasurableSet {v : α → ℝ | MvPolynomial.eval v p = 0} :=
    (isClosed_eq p.continuous_eval continuous_const).measurableSet
  have hp : MeasurableSet {v : α → ℝ | 0 < MvPolynomial.eval v p} :=
    (isOpen_lt continuous_const p.continuous_eval).measurableSet
  by_cases ha : a = 0 <;> by_cases hb : 0 < a
  · exact False.elim (by simpa [ha] using hb)
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.inter hp.compl
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.compl.inter hp
  · simpa [RealSignEquivalent, ha, hb, Set.inter_def] using hz.compl.inter hp.compl

theorem polynomialSignDetermined_borel {α : Type*}
    (A : Finset (MvPolynomial α ℝ)) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined A S) :
    @MeasurableSet (α → ℝ) (borel (α → ℝ)) S := by
  borelize (α → ℝ)
  obtain ⟨R, hR⟩ := polynomialSignDetermined_finite_sign_classes A S hS
  rw [hR]
  apply Finset.measurableSet_biUnion
  intro r _
  have h := A.measurableSet_biInter
    (fun p _ => realSignEquivalent_polynomial_borel (MvPolynomial.eval r p) p)
  simpa only [Set.setOf_forall] using h

theorem hasPolynomialSignDescription_borel {α : Type*}
    {S : Set (α → ℝ)} (hS : HasPolynomialSignDescription S) :
    @MeasurableSet (α → ℝ) (borel (α → ℝ)) S := by
  obtain ⟨A, hA⟩ := hS
  exact polynomialSignDetermined_borel A S hA

end PaperI
