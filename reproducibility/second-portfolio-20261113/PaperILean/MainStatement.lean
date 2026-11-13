import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Targets only. No proof of the main theorem is asserted in this file.
The coefficient representation/quotient bridge and all analytic proof obligations
are listed in reports/CorrespondenceReport.md. -/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
namespace PaperI

abbrev PhysicalSpace := Fin 3 → ℝ
abbrev BoundedExponent (k : ℕ) := Fin 3 → Fin (k + 1)

def totalDegree {k : ℕ} (α : BoundedExponent k) : ℕ :=
  ∑ i, (α i).val

/-- Every nonconstant monomial of total degree at most k, exactly once. -/
def MonomialIndex (k : ℕ) :=
  {α : BoundedExponent k // 1 ≤ totalDegree α ∧ totalDegree α ≤ k}

instance (k : ℕ) : Fintype (MonomialIndex k) := by
  unfold MonomialIndex
  infer_instance

abbrev CoefficientSpace (k : ℕ) := MonomialIndex k → ℝ

/-- Explicit product Lebesgue measure in the monomial coefficients. -/
def coefficientMeasure (k : ℕ) : Measure (CoefficientSpace k) :=
  Measure.pi fun _ => (volume : Measure ℝ)

def physicalMeasure : Measure PhysicalSpace :=
  Measure.pi fun _ => (volume : Measure ℝ)

def dimension (k : ℕ) : ℕ := (k + 3).choose 3 - 1
def chi (k : ℕ) : ℕ := (k + 3).choose 4

/-- The canonical representative has constant coefficient zero. -/
def phase {k : ℕ} (F : CoefficientSpace k) (x : PhysicalSpace) : ℝ := by
  classical
  exact ∑ α, F α * ∏ i, x i ^ (α.val i).val

def unitCube : Set PhysicalSpace :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

def cubeIntegral {k : ℕ} (F : CoefficientSpace k) : ℂ :=
  ∫ x in unitCube, Complex.exp (Complex.I * (phase F x : ℂ)) ∂physicalMeasure

def amplitudeIntegral {k : ℕ} (a : PhysicalSpace → ℂ)
    (F : CoefficientSpace k) : ℂ :=
  ∫ x, a x * Complex.exp (Complex.I * (phase F x : ℂ)) ∂physicalMeasure

def SmoothCompactAmplitude (a : PhysicalSpace → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a ∧ HasCompactSupport a

/-- Audit bridge: smooth means every finite differentiability order, not analytic.
The inner top of `ℕ∞` is deliberately coerced into `WithTop ℕ∞`. -/
theorem smoothCompactAmplitude_iff (a : PhysicalSpace → ℂ) :
    SmoothCompactAmplitude a ↔
      ((∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) a) ∧ HasCompactSupport a) := by
  unfold SmoothCompactAmplitude
  exact and_congr contDiff_infty Iff.rfl

/-- A concrete finite smooth seminorm. Its finiteness for smooth compactly
supported amplitudes, and norm-equivalence bridges, are unproved targets. -/
def smoothSeminorm (m : ℕ) (a : PhysicalSpace → ℂ) : ℝ≥0∞ :=
  ⨆ r : Fin (m + 1), ⨆ x : PhysicalSpace,
    ENNReal.ofReal ‖iteratedFDeriv ℝ r.val a x‖

/-- Operational norm-control formulation of Theorem 1.1(ii) and Proposition 2.8.
m and C are chosen before a, for a fixed compact support K and exponent p.
This is a proposed quantitative target, not a proved translation bridge. -/
def SmoothUniformBound (k : ℕ) (p : ℝ) : Prop :=
  ∀ K : Set PhysicalSpace, IsCompact K →
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : PhysicalSpace → ℂ, SmoothCompactAmplitude a → tsupport a ⊆ K →
        eLpNorm (amplitudeIntegral a : CoefficientSpace k → ℂ)
          (ENNReal.ofReal p) (coefficientMeasure k) ≤ ENNReal.ofReal C * smoothSeminorm m a

/-- Proposed complete main statement. Real p is finite by its type; no p≥1
assumption is added. The upper and lower directions remain one equivalence.
Only part (ii) is restricted to p>chi+3. -/
def MainStatement : Prop :=
  ∀ k : ℕ, 14 ≤ k → ∀ p : ℝ, 0 < p →
    (MemLp (cubeIntegral : CoefficientSpace k → ℂ) (ENNReal.ofReal p)
      (coefficientMeasure k) ↔ (chi k : ℝ) + 3 < p) ∧
    ((chi k : ℝ) + 3 < p →
      (∀ a : PhysicalSpace → ℂ, SmoothCompactAmplitude a →
        MemLp (amplitudeIntegral a : CoefficientSpace k → ℂ) (ENNReal.ofReal p)
          (coefficientMeasure k)) ∧ SmoothUniformBound k p)

#print axioms MainStatement
#print axioms SmoothUniformBound
#print axioms smoothCompactAmplitude_iff

end PaperI
