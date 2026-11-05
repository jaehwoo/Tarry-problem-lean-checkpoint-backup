import PaperILean.NormalFibersJets
import PaperILean.NormalFibersCount

/-! The complete finite-normal-fiber stage, I3258--I3261 and I3269--I3274.
The transverse Jacobian statement in part (ii) is separate. -/

noncomputable section
namespace PaperI.NormalFibers

/-- The source affine map determines all four free frame parameters. -/
theorem framePoint_injective (e f : ℝ) :
    Function.Injective (fun w : Fin 4 → ℝ => framePoint w e f) := by
  intro u v huv
  have hz := congrFun huv (0 : Fin 3 → ℝ)
  have hy := congrFun huv (![0,1,0] : Fin 3 → ℝ)
  have hzz := congrFun huv (![0,0,1] : Fin 3 → ℝ)
  have hc : u 0 = v 0 := by simpa [framePoint] using congrFun hz (0 : Fin 3)
  have ha : u 1 = v 1 := by
    have h := congrFun hy (0 : Fin 3)
    simp [framePoint] at h
    linarith
  have hb : u 2 = v 2 := by
    have h := congrFun hzz (0 : Fin 3)
    simp [framePoint] at h
    linarith
  have hd : u 3 = v 3 := by
    have h := congrFun hzz (1 : Fin 3)
    simpa [framePoint] using h
  ext i
  fin_cases i
  · exact hc
  · exact ha
  · exact hb
  · exact hd

theorem normalizedFrames_eq_scalarFrames (G : Poly) (e f : ℝ) :
    normalizedFrames G e f = scalarFrames (linePolynomial G e f)
      (firstAt G e f 1) (firstAt G e f 2)
      (secondAt G e f 0 0) (secondAt G e f 0 1) (secondAt G e f 0 2)
      (secondAt G e f 1 1) (secondAt G e f 1 2) (secondAt G e f 2 2) := by
  ext w
  simp only [normalizedFrames, scalarFrames, Set.mem_setOf_eq,
    eval_pullback_zero, first_x, first_y, first_z, second_yy, second_yz, second_zz,
    linePolynomial_eval, linePolynomial_derivative, valueAt]

end PaperI.NormalFibers

namespace PaperI

/-- Entire part (i) of the source lemma: actual normalized frames, in their
injective source coordinates, are finite with the stated degree bound. -/
theorem finite_normal_fibers_stage (G : MvPolynomial (Fin 3) ℝ) (D : ℕ)
    (hdegree : G.totalDegree ≤ D) (e f : ℝ) :
    (NormalFibers.normalizedFrames G e f).Finite ∧
      (NormalFibers.normalizedFrames G e f).ncard ≤ 3 * D := by
  rw [NormalFibers.normalizedFrames_eq_scalarFrames]
  obtain ⟨hf,hcard⟩ := NormalFibers.scalarFrames_finite_ncard
    (NormalFibers.linePolynomial G e f)
    (NormalFibers.firstAt G e f 1) (NormalFibers.firstAt G e f 2)
    (NormalFibers.secondAt G e f 0 0) (NormalFibers.secondAt G e f 0 1)
    (NormalFibers.secondAt G e f 0 2) (NormalFibers.secondAt G e f 1 1)
    (NormalFibers.secondAt G e f 1 2) (NormalFibers.secondAt G e f 2 2)
  exact ⟨hf,hcard.trans (Nat.mul_le_mul_left 3
    ((NormalFibers.linePolynomial_degree G e f).trans hdegree))⟩

end PaperI
