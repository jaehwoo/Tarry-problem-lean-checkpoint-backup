import PaperILean.SPDFrameCompactness

/-! Existence part of Paper I Lemma 2.3(i), proof line 246.
The extreme-value theorem is applied to a proved compact nonempty sublevel.
Uniqueness and smooth dependence are not asserted here. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem exists_FrameEnergy_posDef_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.PosDef ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℝ, T.PosDef → FrameEnergy F c lam S ≤ FrameEnergy F c lam T := by
  let M := FrameEnergy F c lam 1
  let K := {S : Matrix (Fin 3) (Fin 3) ℝ | S.PosDef ∧ FrameEnergy F c lam S ≤ M}
  have hc : IsCompact K := isCompact_FrameEnergy_posDef_sublevel F c lam hlam M
  have hn : K.Nonempty := ⟨1, Matrix.PosDef.one, le_rfl⟩
  have hf : ContinuousOn (FrameEnergy F c lam) K :=
    (continuousOn_FrameEnergy F c lam).mono (fun S hS => hS.1.det_pos)
  obtain ⟨S, hS, hmin⟩ := hc.exists_isMinOn hn hf
  refine ⟨S, hS.1, fun T hT => ?_⟩
  by_cases hE : FrameEnergy F c lam T ≤ M
  · exact hmin ⟨hT, hE⟩
  · exact hS.2.trans (le_of_not_ge hE)

theorem exists_FrameEnergy_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.PosDef ∧
      ∀ B : PositiveFrame, FrameEnergy F c lam S ≤ FrameEnergy F c lam B.val := by
  obtain ⟨S, hS, hmin⟩ := exists_FrameEnergy_posDef_minimum F c lam hlam
  refine ⟨S, hS, fun B => ?_⟩
  rw [← spdFrameRepresentative_energy F c lam B]
  exact hmin _ (spdFrameRepresentative_posDef B)

theorem exists_ellipsoidFrameEnergy_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ E : PositiveFrameEllipsoid, ∀ D : PositiveFrameEllipsoid,
      ellipsoidFrameEnergy F c lam E ≤ ellipsoidFrameEnergy F c lam D := by
  obtain ⟨S, hS, hmin⟩ := exists_FrameEnergy_minimum F c lam hlam
  refine ⟨Quotient.mk positiveFrameGramSetoid ⟨S, hS.det_pos⟩, ?_⟩
  intro D
  induction D using Quotient.inductionOn with
  | h B => exact hmin B

theorem exists_sourceFrameEnergy_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S.PosDef ∧
      ∀ B : PositiveFrame, sourceFrameEnergy F c CX C0 R S ≤ sourceFrameEnergy F c CX C0 R B.val :=
  exists_FrameEnergy_minimum F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR).le

end PaperI
