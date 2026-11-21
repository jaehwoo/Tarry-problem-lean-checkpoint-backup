import Revision.OriginalWindow
import PaperILean.Nov18CollarAssignedPhase

noncomputable section
namespace PaperI.CollarVolume
open Set MeasureTheory CommonNullAssignment BoundedCharacteristic OriginalHaarWindowMeasures
open scoped ContDiff

theorem revised_assigned_volume {k : ℕ} (hk : 9≤k) (z rate sizePow K g pp sp wc : ℕ)
    (hCell : PublishedSemialgebraicCellDecomposition) (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality) (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity) (hPiece : PublishedPiecewiseNashExtensions)
    (hH : PublishedSemialgebraicHardtTriviality) (hQQE : PublishedQuantitativeRealQE) :
    ∃ defect loss : ℕ, ∀ m : ℕ, 2≤m → m≤k/2 →
      ∀ {σ ι : Type} [DecidableEq ι] {P L δ M T Λ U B d₁ : ℝ}, 2≤P → 1≤L → δ≤(P^defect)⁻¹ →
      ∀ (F : OriginalNullFamily k σ) {cmp cf norm rp ap fp pack coord : ℕ}
      {labels : Finset ι} {rep : (NullScalarParameters k σ → ℝ) → ι → Plane} {fixed : ι → Fin 6 → ℝ}
      {X : OriginalNullModelInput F P δ M T Λ U B rate cmp cf norm rp ap fp pack labels rep fixed}
      (S : OriginalCommonNullAssignment F P δ M T Λ U B d₁ (2*k+1) z rate cmp cf norm rp ap fp pack coord labels rep fixed X),
      ∀ {m₀ τ : ℝ}, RevisedAssignmentReadout S sizePow K m₀ τ →
      U≤P^g → B≤P^g →
      ∀ (i : ι) (E : Set (CoefficientSpace k)),
      (∀ J∈E, ∃ p : NullScalarParameters k σ → ℝ, ∃ j : Fin S.bands.count,
        p ∘ Sum.inl=J ∧ i∈S.piece p j ∧ (S.route j p=.cap ∨ S.route j p=.transverseCollar) ∧
        (S.tag j p).1=L ∧ CollarH3.NullSheetData m (p ∘ Sum.inl) (F.E p) (F.root p) (F.slope p) P pp sp) →
      (∀ J∈E, coefficientEuclideanNorm (originalUpperCoefficientPullback J (fixed i))≤P^wc) →
      (∀ J∈E, (P^wc)⁻¹≤originalHaarPhysicalLeastSingularValue .H3 (originalUpperCoefficientPullback J (fixed i))) →
      volume E ≤ ENNReal.ofReal (P^loss*L^(-CollarExponentMargins.beta k m)) ∧
      CollarExponentMargins.beta k m =
        SurfaceExponentMargins.scalarH (k-m+2)+CollarExponentMargins.chiR k-
        CollarExponentMargins.chiR (k-m+2)-6*(k:ℝ)-2 ∧
      CollarExponentMargins.chiR k+4 ≤ CollarExponentMargins.beta k m := by
  obtain ⟨defect,loss,h⟩ := assigned_collar_volume hk z rate (sizePow+1) K g pp sp wc
    hCell hPath hHardt hQE hNash hPiece hH hQQE
  refine ⟨defect,loss,?_⟩
  intro m hm hmk σ ι _ P L δ M T Λ U B d₁ hP hL hδ F cmp cf norm rp ap fp pack coord labels rep fixed X S m₀ τ hS
  apply h m hm hmk hP hL hδ F S
  intro p j hj hr
  obtain ⟨e,he,es,hes,fs,hfs,fd,hfd,Q,hBudget,_⟩ := (hS p j hj).2 hr
  exact ⟨e,he,es,hes,fs,hfs,fd,hfd,Q,hBudget⟩

end PaperI.CollarVolume
