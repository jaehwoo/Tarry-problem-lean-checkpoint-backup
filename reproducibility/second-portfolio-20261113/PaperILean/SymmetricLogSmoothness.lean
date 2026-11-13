import PaperILean.MatrixTraceSquareDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Smoothness of the actual CFC logarithm on the positive symmetric cone.
Uses the checked invertible exponential differential, including collisions.
This extends the recorded inverse-exponential proof route, not Lewis--Sendov. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm Topology
namespace PaperI

theorem contDiff_matrix_exp {n : ℕ} :
    ContDiff ℝ ⊤ (NormedSpace.exp ℝ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
  contDiff_iff_contDiffAt.mpr (fun A => (NormedSpace.exp_analytic A).contDiffAt)

theorem contDiff_symmetricMatrixExp {n : ℕ} :
    ContDiff ℝ ⊤ (symmetricMatrixExp : SymmetricMatrix n → SymmetricMatrix n) := by
  have h := (symmetricMatrixProjection n).contDiff.comp
    (contDiff_matrix_exp.comp (symmetricMatrixIncl n).contDiff)
  simpa only [Function.comp_def, symmetricMatrixProjection_exp] using h

theorem contDiffAt_symmetricMatrixLog {n : ℕ} (A : SymmetricMatrix n)
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    ContDiffAt ℝ ⊤ symmetricMatrixLog A := by
  let X := symmetricMatrixLog A
  have he := (contDiff_symmetricMatrixExp (n := n)).contDiffAt (x := X)
  have hd := (symmetricMatrixExp_hasStrictFDerivAt X).hasFDerivAt
  have hi := he.to_localInverse hd (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
  have hu := (he.hasStrictFDerivAt' hd (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).localInverse_unique
    (Filter.Eventually.of_forall (fun Y : SymmetricMatrix n => symmetricMatrixLog_exp Y))
  have hc : ContDiffAt ℝ ⊤ symmetricMatrixLog (symmetricMatrixExp X) :=
    hi.congr_of_eventuallyEq hu
  simpa only [X, symmetricMatrixExp_log A hA] using hc

theorem contDiffAt_symmetricLogEnergy {n : ℕ} (A : SymmetricMatrix n)
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    ContDiffAt ℝ ⊤ symmetricLogEnergy A := by
  have hl := (symmetricMatrixIncl n).contDiff.contDiffAt.comp A
    (contDiffAt_symmetricMatrixLog A hA)
  exact (matrixTraceCLM n).contDiff.contDiffAt.comp A (hl.pow 2)

end PaperI
