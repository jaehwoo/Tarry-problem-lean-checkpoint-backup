import PaperILean.RectangularSingularValues
import PaperILean.AugmentedPhysicalAffine
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! The literal three-by-four affine-field matrix at I3251. Its last column
is the translation, and its Frobenius norm is the Euclidean norm of all twelve
entries. Vanishing second singular value and normalization give a nonzero
rank-one factorization, without any invertibility assumption on a physical map. -/

noncomputable section
open scoped BigOperators

namespace PaperI.RankOneAffineMatrix

noncomputable def affineFieldMatrix (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 4) ℝ :=
  fun i j => Fin.lastCases (b i) (fun q => N i q) j

@[simp] theorem affineFieldMatrix_last (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    affineFieldMatrix b N i (Fin.last 3) = b i := by
  exact Fin.lastCases_last

@[simp] theorem affineFieldMatrix_castSucc (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    affineFieldMatrix b N i j.castSucc = N i j := by
  simp [affineFieldMatrix]

def affineFieldFrobenius (b : PhysicalSpace) (N : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, affineFieldMatrix b N i j ^ 2)

theorem affineFieldMatrix_ne_zero_of_normalized (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (hunit : affineFieldFrobenius b N = 1) :
    affineFieldMatrix b N ≠ 0 := by
  intro hz
  simp [affineFieldFrobenius, hz] at hunit

theorem matrix_rank_le_one_factor (M : Matrix (Fin 3) (Fin 4) ℝ)
    (hM : M ≠ 0) (hr : M.rank ≤ 1) :
    ∃ u : PhysicalSpace, u ≠ 0 ∧ ∃ a : Fin 4 → ℝ, a ≠ 0 ∧
      ∀ i j, M i j = u i * a j := by
  classical
  let W := Submodule.span ℝ (Set.range M.col)
  have hd : Module.finrank ℝ W ≤ 1 := by
    simpa only [W, ← Matrix.rank_eq_finrank_span_cols] using hr
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := ℝ) (V := W)).mp hd
  have hcol (j : Fin 4) : M.col j ∈ W :=
    Submodule.subset_span (Set.mem_range_self j)
  choose a ha using fun j : Fin 4 => hu ⟨M.col j, hcol j⟩
  have hfactor (i : Fin 3) (j : Fin 4) : M i j = (u : PhysicalSpace) i * a j := by
    have h := congrArg (fun w : W => (w : PhysicalSpace) i) (ha j)
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      mul_comm] using h.symm
  have hu0 : (u : PhysicalSpace) ≠ 0 := by
    intro hz
    apply hM
    ext i j
    simp only [hfactor, hz, Pi.zero_apply, zero_mul, Matrix.zero_apply]
  have ha0 : a ≠ 0 := by
    intro hz
    apply hM
    ext i j
    simp only [hfactor, hz, Pi.zero_apply, mul_zero, Matrix.zero_apply]
  exact ⟨u, hu0, a, ha0, hfactor⟩

theorem normalized_factor_of_sigma2_zero (b : PhysicalSpace)
    (N : Matrix (Fin 3) (Fin 3) ℝ) (hunit : affineFieldFrobenius b N = 1)
    (hσ : descendingSingularValues (affineFieldMatrix b N) (1 : Fin 4) = 0) :
    ∃ u : PhysicalSpace, u ≠ 0 ∧ ∃ a : Fin 4 → ℝ, a ≠ 0 ∧
      (∀ i, b i = u i * a (Fin.last 3)) ∧
      (∀ i j, N i j = u i * a j.castSucc) := by
  have hr : (affineFieldMatrix b N).rank ≤ 1 :=
    (descendingSingularValues_eq_zero_iff_rank _ (1 : Fin 4)).mp hσ
  obtain ⟨u, hu, a, ha, hfactor⟩ := matrix_rank_le_one_factor
    (affineFieldMatrix b N) (affineFieldMatrix_ne_zero_of_normalized b N hunit) hr
  refine ⟨u, hu, a, ha, ?_, ?_⟩
  · intro i
    simpa only [affineFieldMatrix_last] using hfactor i (Fin.last 3)
  · intro i j
    simpa only [affineFieldMatrix_castSucc] using hfactor i j.castSucc

end PaperI.RankOneAffineMatrix
