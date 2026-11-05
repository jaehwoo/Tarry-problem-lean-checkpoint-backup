import PaperILean.RealPolynomialDefinability
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.DenselyOrdered

/-! I623-638: an explicit finite polynomial-sign interface for the missing
real elimination theorem. The interface is NOT inferred from first-order
definability here. Equalities alone are not the required sign conditions. -/

noncomputable section
namespace PaperI
attribute [local instance] Classical.propDecidable

def RealSignEquivalent (a b : ℝ) : Prop :=
  (a = 0 ↔ b = 0) ∧ (0 < a ↔ 0 < b)

theorem realSignEquivalent_refl (a : ℝ) : RealSignEquivalent a a :=
  ⟨Iff.rfl, Iff.rfl⟩

theorem realSignEquivalent_nonneg {a b : ℝ} (h : RealSignEquivalent a b) :
    0 ≤ a ↔ 0 ≤ b := by
  constructor
  · intro ha
    rcases eq_or_lt_of_le ha with ha | ha
    · exact le_of_eq (h.1.mp ha.symm).symm
    · exact (h.2.mp ha).le
  · intro hb
    rcases eq_or_lt_of_le hb with hb | hb
    · exact le_of_eq (h.1.mpr hb.symm).symm
    · exact (h.2.mpr hb).le

def PolynomialSignDetermined {α : Type*} (A : Finset (MvPolynomial α ℝ))
    (S : Set (α → ℝ)) : Prop :=
  ∀ x y, (∀ p ∈ A, RealSignEquivalent (MvPolynomial.eval x p) (MvPolynomial.eval y p)) →
    (x ∈ S ↔ y ∈ S)

def HasPolynomialSignDescription {α : Type*} (S : Set (α → ℝ)) : Prop :=
  ∃ A : Finset (MvPolynomial α ℝ), PolynomialSignDetermined A S

theorem polynomialSignDetermined_mono {α : Type*}
    {A B : Finset (MvPolynomial α ℝ)} {S : Set (α → ℝ)}
    (h : PolynomialSignDetermined A S) (hAB : A ⊆ B) : PolynomialSignDetermined B S :=
  fun x y hxy => h x y (fun p hp => hxy p (hAB hp))

theorem polynomialSignDetermined_compl {α : Type*}
    {A : Finset (MvPolynomial α ℝ)} {S : Set (α → ℝ)}
    (h : PolynomialSignDetermined A S) : PolynomialSignDetermined A Sᶜ :=
  fun x y hxy => not_congr (h x y hxy)

theorem polynomialSignDetermined_inter {α : Type*}
    {A B : Finset (MvPolynomial α ℝ)} {S T : Set (α → ℝ)}
    (hS : PolynomialSignDetermined A S) (hT : PolynomialSignDetermined B T) :
    PolynomialSignDetermined (A ∪ B) (S ∩ T) := by
  classical
  intro x y hxy
  exact and_congr (hS x y (fun p hp => hxy p (Finset.mem_union_left B hp)))
    (hT x y (fun p hp => hxy p (Finset.mem_union_right A hp)))

theorem polynomialSignDetermined_union {α : Type*}
    {A B : Finset (MvPolynomial α ℝ)} {S T : Set (α → ℝ)}
    (hS : PolynomialSignDetermined A S) (hT : PolynomialSignDetermined B T) :
    PolynomialSignDetermined (A ∪ B) (S ∪ T) := by
  classical
  intro x y hxy
  exact or_congr (hS x y (fun p hp => hxy p (Finset.mem_union_left B hp)))
    (hT x y (fun p hp => hxy p (Finset.mem_union_right A hp)))

theorem polynomialSignDetermined_zero {α : Type*} (p : MvPolynomial α ℝ) :
    PolynomialSignDetermined {p} {x | MvPolynomial.eval x p = 0} := by
  intro x y h
  exact (h p (Finset.mem_singleton_self p)).1

theorem polynomialSignDetermined_pos {α : Type*} (p : MvPolynomial α ℝ) :
    PolynomialSignDetermined {p} {x | 0 < MvPolynomial.eval x p} := by
  intro x y h
  exact (h p (Finset.mem_singleton_self p)).2

theorem polynomialSignDetermined_nonneg {α : Type*} (p : MvPolynomial α ℝ) :
    PolynomialSignDetermined {p} {x | 0 ≤ MvPolynomial.eval x p} := by
  intro x y h
  exact realSignEquivalent_nonneg (h p (Finset.mem_singleton_self p))

theorem polynomialSignDetermined_empty {α : Type*} :
    PolynomialSignDetermined (∅ : Finset (MvPolynomial α ℝ)) ∅ := by
  intro x y _
  rfl

theorem polynomialSignDetermined_univ {α : Type*} :
    PolynomialSignDetermined (∅ : Finset (MvPolynomial α ℝ)) Set.univ := by
  intro x y _
  rfl

end PaperI
