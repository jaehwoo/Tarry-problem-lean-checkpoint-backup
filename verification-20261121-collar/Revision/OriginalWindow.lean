import Revision.Assignment
import PaperILean.CommonNullRQSpecialization

noncomputable section
namespace PaperI.CommonNullAssignment
open PaperI.BoundedCharacteristic

theorem revised_assignment_from_rq
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (hQQE : PublishedQuantitativeRealQE)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity) (hPiece : PublishedPiecewiseNashExtensions)
    {k : ℕ} (hk : 1≤k) {σ ι : Type} [Fintype σ] [DecidableEq ι]
    (F : OriginalNullFamily k σ)
    (N K mPow scalePow ratePow widthPow sizePow physPow qPow compPow Cf normPow rPow aPow fPow packPow : ℕ)
    (C₀ cutPow : ℝ) (hC₀ : 0≤C₀) :
    ∃ e : ℕ, ∀ {P m τ M δ d₁ c CP cR Λ U B : ℝ} {D : Fin 3 → ℝ},
      (Q : OriginalNullLocalScaleInput P m τ M δ c CP cR C₀ cutPow K mPow scalePow ratePow widthPow sizePow) →
      (R : OriginalNullRQInput F P d₁ D physPow qPow) →
      ∀ (labels : Finset ι) (rep : (NullScalarParameters k σ → ℝ) → ι → Plane) (fixed : ι → Fin 6 → ℝ)
      (X : OriginalNullCoreInput F P δ M Λ U B ratePow compPow Cf normPow rPow aPow fPow packPow labels rep fixed),
      let coordPow := physPow+qPow+5
      let T := P^coordPow*d₁⁻¹
      ∃ S : OriginalCommonNullAssignment F P δ M T Λ U B d₁ N e ratePow compPow Cf normPow rPow aPow fPow packPow coordPow
        labels rep fixed (R.model Q.P_ge X), RevisedAssignmentReadout S sizePow K m τ := by
  obtain ⟨e,h⟩ := revised_common_null_assignment hDD hQQE hCell hHardt hQE hNash hPiece hk (ι:=ι) F
    N K mPow scalePow ratePow widthPow sizePow (physPow+qPow+5) compPow Cf normPow rPow aPow fPow packPow C₀ cutPow hC₀
  refine ⟨e,?_⟩
  intro P m τ M δ d₁ c CP cR Λ U B D Q R labels rep fixed X coordPow T
  have hT := (original_null_rq_window F Q.P_ge R.d1_pos R.d1_le R.diag_pos R.diag_inverse R.physical).1
  exact h ⟨Q,hT,R.d1_pos,R.d1_le,le_rfl⟩ labels rep fixed (R.model Q.P_ge X)

end PaperI.CommonNullAssignment
