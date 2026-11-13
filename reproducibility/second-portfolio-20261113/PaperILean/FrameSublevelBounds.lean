import PaperILean.SPDFrameRepresentative

/-! Quantitative spectral, determinant and entry bounds for the SPD sublevels
at Paper I 246. Constants depend only on the sublevel height M. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem FrameEnergy_sublevel_det_lower {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef)
    (M : ℝ) (hM : FrameEnergy F c lam S ≤ M) :
    (Real.exp (-M / 2)) ^ 3 ≤ S.det := by
  rw [hS.isHermitian.det_eq_prod_eigenvalues]
  simpa using Finset.prod_le_prod
    (s := Finset.univ) (f := fun _ : Fin 3 => Real.exp (-M / 2))
    (fun i _ => (Real.exp_pos _).le)
    (fun i _ => (FrameEnergy_sublevel_eigenvalue_bounds F c lam hlam S hS M hM i).1)

theorem FrameEnergy_sublevel_HS_sq_upper {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef)
    (M : ℝ) (hM : FrameEnergy F c lam S ≤ M) :
    (matrixFullHSNorm S) ^ 2 ≤ 3 * (1 + Real.sqrt M) ^ 2 := by
  rw [matrixFullHSNorm_sq_eq_sum_eigenvalues_sq S hS.isHermitian]
  have hh : ∀ i : Fin 3, (hS.isHermitian.eigenvalues i) ^ 2 ≤ (1 + Real.sqrt M) ^ 2 := by
    intro i
    exact pow_le_pow_left₀ (hS.eigenvalues_pos i).le
      (FrameEnergy_sublevel_eigenvalue_bounds F c lam hlam S hS M hM i).2 2
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)

theorem matrix_entry_sq_le_fullHS_sq {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : (S i j) ^ 2 ≤ (matrixFullHSNorm S) ^ 2 := by
  rw [matrixFullHSNorm_sq]
  exact (Finset.single_le_sum (fun j _ => sq_nonneg (S i j)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (S i j)))
      (Finset.mem_univ i))

theorem FrameEnergy_sublevel_entry_bounds {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef)
    (M : ℝ) (hM : FrameEnergy F c lam S ≤ M) (i j : Fin 3) :
    |S i j| ≤ 3 * (1 + Real.sqrt M) := by
  have hh := (matrix_entry_sq_le_fullHS_sq S i j).trans
    (FrameEnergy_sublevel_HS_sq_upper F c lam hlam S hS M hM)
  have hs := Real.sqrt_nonneg M
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (S i j - 3 * (1 + Real.sqrt M)),
    sq_nonneg (S i j + 3 * (1 + Real.sqrt M))]

theorem FrameEnergy_posDef_sublevel_empty {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ) (hM : M < 3) :
    {S : Matrix (Fin 3) (Fin 3) ℝ | S.PosDef ∧ FrameEnergy F c lam S ≤ M} = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro S ⟨hS, hE⟩
  exact (not_le_of_gt hM) ((FrameEnergy_posDef_ge_three F c lam hlam S hS).trans hE)

end PaperI
