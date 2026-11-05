import PaperILean.MainStatement

/-! The complete monomial coefficient model in every finite dimension.
The old three-dimensional definitions remain unchanged and specialize by rfl.
No main theorem or determinant character is assumed here. -/

open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
namespace PaperI.AllDim

abbrev PhysicalSpace (n : ℕ) := Fin n → ℝ
abbrev BoundedExponent (n k : ℕ) := Fin n → Fin (k + 1)

def totalDegree {n k : ℕ} (α : BoundedExponent n k) : ℕ := ∑ i, (α i).val

def MonomialIndex (n k : ℕ) :=
  {α : BoundedExponent n k // 1 ≤ totalDegree α ∧ totalDegree α ≤ k}

instance monomialIndexFintype (n k : ℕ) : Fintype (MonomialIndex n k) := by
  unfold MonomialIndex
  infer_instance

abbrev CoefficientSpace (n k : ℕ) := MonomialIndex n k → ℝ

def coefficientMeasure (n k : ℕ) : Measure (CoefficientSpace n k) :=
  Measure.pi fun _ => (volume : Measure ℝ)

def physicalMeasure (n : ℕ) : Measure (PhysicalSpace n) :=
  Measure.pi fun _ => (volume : Measure ℝ)

def dimension (n k : ℕ) : ℕ := (k + n).choose n - 1
def chi (n k : ℕ) : ℕ := (k + n).choose (n + 1)

def phase {n k : ℕ} (F : CoefficientSpace n k) (x : PhysicalSpace n) : ℝ := by
  classical
  exact ∑ α, F α * ∏ i, x i ^ (α.val i).val

theorem phase_three {k : ℕ} (F : CoefficientSpace 3 k) (x : PhysicalSpace 3) :
    phase F x = PaperI.phase F x := rfl

theorem coefficientMeasure_three (k : ℕ) :
    coefficientMeasure 3 k = PaperI.coefficientMeasure k := rfl

theorem physicalMeasure_three : physicalMeasure 3 = PaperI.physicalMeasure := rfl

theorem chi_three (k : ℕ) : chi 3 k = PaperI.chi k := rfl

theorem dimension_three (k : ℕ) : dimension 3 k = PaperI.dimension k := rfl

instance monomialIndexIsEmptyDimZero (k : ℕ) : IsEmpty (MonomialIndex 0 k) := by
  refine ⟨fun α => ?_⟩
  have h := α.property.1
  simp [totalDegree] at h

instance monomialIndexIsEmptyDegreeZero (n : ℕ) : IsEmpty (MonomialIndex n 0) := by
  refine ⟨fun α => ?_⟩
  have h := α.property
  omega

theorem phase_dim_zero {k : ℕ} (F : CoefficientSpace 0 k) (x : PhysicalSpace 0) :
    phase F x = 0 := by simp [phase]

theorem phase_degree_zero {n : ℕ} (F : CoefficientSpace n 0) (x : PhysicalSpace n) :
    phase F x = 0 := by simp [phase]

end PaperI.AllDim
