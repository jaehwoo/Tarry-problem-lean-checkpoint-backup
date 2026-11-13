import PaperILean.UniversalPolynomialFamily
import PaperILean.PolynomialSignDescription

/-! A finite Boolean table and a fixed universal coefficient family encode every
set determined by a bounded list of polynomial signs. Unattained sign patterns,
zero or repeated polynomials, and the empty list impose no extra hypotheses. -/

noncomputable section

namespace PaperI

attribute [local instance] Classical.propDecidable

def polynomialFamilySignCode {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial α ℝ) (x : α → ℝ) : Fin s → Bool × Bool :=
  fun i => (decide (MvPolynomial.eval x (p i) = 0), decide (0 < MvPolynomial.eval x (p i)))

theorem polynomialFamilySignCode_eq_iff {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial α ℝ) (x y : α → ℝ) :
    polynomialFamilySignCode p x = polynomialFamilySignCode p y ↔
      ∀ i, RealSignEquivalent (MvPolynomial.eval x (p i)) (MvPolynomial.eval y (p i)) := by
  constructor
  · intro h i
    have hi := congrFun h i
    exact ⟨decide_eq_decide.mp (congrArg Prod.fst hi),
      decide_eq_decide.mp (congrArg Prod.snd hi)⟩
  · intro h
    funext i
    exact Prod.ext (decide_eq_decide.mpr (h i).1) (decide_eq_decide.mpr (h i).2)

def polynomialBooleanSet {α : Type*} {s : ℕ} (p : Fin s → MvPolynomial α ℝ)
    (b : (Fin s → Bool × Bool) → Bool) : Set (α → ℝ) :=
  {x | b (polynomialFamilySignCode p x) = true}

theorem polynomialBooleanSet_signDetermined {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial α ℝ) (b : (Fin s → Bool × Bool) → Bool) :
    PolynomialSignDetermined (Finset.univ.image p) (polynomialBooleanSet p b) := by
  classical
  intro x y hxy
  have hcode : polynomialFamilySignCode p x = polynomialFamilySignCode p y :=
    (polynomialFamilySignCode_eq_iff p x y).mpr
      (fun i => hxy (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  change b (polynomialFamilySignCode p x) = true ↔ b (polynomialFamilySignCode p y) = true
  rw [hcode]

theorem polynomialBooleanSet_hasPolynomialSignDescription {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial α ℝ) (b : (Fin s → Bool × Bool) → Bool) :
    HasPolynomialSignDescription (polynomialBooleanSet p b) := by
  classical
  exact ⟨Finset.univ.image p, polynomialBooleanSet_signDetermined p b⟩

/-- Only realized codes determine membership; the table is false on unrealized codes. -/
theorem polynomialSignDetermined_exists_boolean_table {α : Type*} {s : ℕ}
    (p : Fin s → MvPolynomial α ℝ) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined (Finset.univ.image p) S) :
    ∃ b : (Fin s → Bool × Bool) → Bool, S = polynomialBooleanSet p b := by
  classical
  let b : (Fin s → Bool × Bool) → Bool := fun c =>
    decide (∃ x, x ∈ S ∧ polynomialFamilySignCode p x = c)
  refine ⟨b, ?_⟩
  ext x
  change x ∈ S ↔ decide (∃ y, y ∈ S ∧ polynomialFamilySignCode p y =
    polynomialFamilySignCode p x) = true
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hcode⟩
    apply (hS y x ?_).mp hy
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact (polynomialFamilySignCode_eq_iff p y x).mp hcode i

def universalPolynomialBooleanSet (α : Type*) [Fintype α] (s D : ℕ)
    (b : (Fin s → Bool × Bool) → Bool) :
    Set (((Fin s × (α → Fin (D + 1))) ⊕ α) → ℝ) :=
  polynomialBooleanSet (universalCoefficientPolynomial α s D) b

theorem universalPolynomialBooleanSet_hasPolynomialSignDescription
    (α : Type*) [Fintype α] (s D : ℕ) (b : (Fin s → Bool × Bool) → Bool) :
    HasPolynomialSignDescription (universalPolynomialBooleanSet α s D b) :=
  polynomialBooleanSet_hasPolynomialSignDescription (universalCoefficientPolynomial α s D) b

theorem universalPolynomialBooleanSet_fiber {α : Type*} [Fintype α]
    (s D : ℕ) (p : Fin s → MvPolynomial α ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (b : (Fin s → Bool × Bool) → Bool) :
    {x : α → ℝ | Sum.elim (polynomialFamilyCoefficients D p) x ∈
      universalPolynomialBooleanSet α s D b} = polynomialBooleanSet p b := by
  have hcode (x : α → ℝ) :
      polynomialFamilySignCode (universalCoefficientPolynomial α s D)
        (Sum.elim (polynomialFamilyCoefficients D p) x) = polynomialFamilySignCode p x := by
    funext i
    simp only [polynomialFamilySignCode, universalCoefficientPolynomial_eval s D p hp x i]
  ext x
  change b (polynomialFamilySignCode (universalCoefficientPolynomial α s D)
    (Sum.elim (polynomialFamilyCoefficients D p) x)) = true ↔
      b (polynomialFamilySignCode p x) = true
  rw [hcode]

/-- The finite table is the only discrete choice: polynomial coefficients vary in
one fixed real coordinate space chosen from `α`, `s`, and `D`. -/
theorem polynomialSignDetermined_exists_universal_fiber {α : Type*} [Fintype α]
    (s D : ℕ) (p : Fin s → MvPolynomial α ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (S : Set (α → ℝ))
    (hS : PolynomialSignDetermined (Finset.univ.image p) S) :
    ∃ b : (Fin s → Bool × Bool) → Bool,
      S = {x : α → ℝ | Sum.elim (polynomialFamilyCoefficients D p) x ∈
        universalPolynomialBooleanSet α s D b} := by
  obtain ⟨b, hb⟩ := polynomialSignDetermined_exists_boolean_table p S hS
  exact ⟨b, hb.trans (universalPolynomialBooleanSet_fiber s D p hp b).symm⟩

end PaperI
