import PaperILean.PublishedFormatComponents
import PaperILean.UniformComponentSignFormat
import PaperILean.PublishedBoundedFormatPaths
import PaperILean.OriginalHaarWindowPathCuts

/-! Uniformly many components and uniformly many analytic/sign pieces for
actual polynomial readouts on the same component paths. This applies the
saved published inputs; it does not replace an orbit or pivot bridge by an
assumption. Absolute component locations and ranges can be unbounded. -/
noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The count and subdivision bound precede all polynomial coefficients,
component locations, and endpoint choices. Group-coordinate readouts force
analyticity of the chosen path on the same uniformly bounded pieces as the
phase coefficient derivative signs. -/
theorem published_originalHaar_component_polynomial_paths
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (κ ι : Type) [Fintype κ] [Fintype ι] (s D E : ℕ) :
    ∃ N K : ℕ, ∀ (A : Finset (MvPolynomial κ ℝ)) (S : Set (κ → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ N ∧
      ∀ Q : ι → MvPolynomial κ ℝ, (∀ i, (Q i).totalDegree ≤ E) →
      ∀ z a b : κ → ℝ, a ∈ connectedComponentIn S z → b ∈ connectedComponentIn S z →
      ∃ γ : SemialgebraicUnitPath (connectedComponentIn S z) a b,
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0:ℝ) 1) ∧
        C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          (∀ i : κ, AnalyticOnNhd ℝ (fun t => γ.toFun t i) (Ioo u v)) ∧
          (∀ i : ι, AnalyticOnNhd ℝ (fun t => MvPolynomial.eval (γ.toFun t) (Q i)) (Ioo u v) ∧
            DerivativeSignOn (fun t => MvPolynomial.eval (γ.toFun t) (Q i)) (Ioo u v)) := by
  obtain ⟨N,hN⟩ := published_bounded_sign_format_component_bound hCell.toFiniteConnectedCover
    hHardt.toHardtTriviality hQE κ s D
  obtain ⟨sComp,dComp,hComp⟩ := published_bounded_sign_format_component_sign_format
    hCell hHardt hQE κ s D
  obtain ⟨sPath,dPath,hPaths⟩ := published_bounded_sign_format_paths
    hPath hHardt hQE κ sComp dComp
  obtain ⟨K,hCuts⟩ := published_originalHaar_polynomial_path_cuts
    hCell.toFiniteConnectedCover hHardt hQE hNash hPiece κ (κ ⊕ ι)
    sComp dComp sPath dPath (max E 1)
  refine ⟨N,K,?_⟩
  intro A S hAc hAd hAS
  refine ⟨(hN A S hAc hAd hAS).1,(hN A S hAc hAd hAS).2,?_⟩
  intro Q hQ z a b ha hb
  obtain ⟨B,hBc,hBd,hBS⟩ := hComp A S hAc hAd hAS
  obtain ⟨γ,P,hPc,hPd,hP⟩ := hPaths B (connectedComponentIn S z) hBc hBd
    (hBS z) (isPreconnected_connectedComponentIn) a ha b hb
  let QQ : κ ⊕ ι → MvPolynomial κ ℝ := Sum.elim MvPolynomial.X Q
  have hQQ : ∀ i, (QQ i).totalDegree ≤ max E 1 := by
    intro i
    cases i with
    | inl i => exact (by simp [QQ] : (QQ (Sum.inl i)).totalDegree ≤ 1).trans (Nat.le_max_right _ _)
    | inr i => exact (hQ i).trans (Nat.le_max_left _ _)
  obtain ⟨C,hC0,hC1,hCI,hCK,hCprops⟩ := hCuts (connectedComponentIn S z) B hBc hBd
    (hBS z) a b γ P hPc hPd hP QQ hQQ
  refine ⟨γ,C,hC0,hC1,hCI,hCK,?_⟩
  intro u hu v hv huv hgap
  constructor
  · intro i
    simpa only [QQ,Sum.elim_inl,MvPolynomial.eval_X] using
      (hCprops u hu v hv huv hgap (Sum.inl i)).1
  · intro i
    simpa only [QQ,Sum.elim_inr] using
      hCprops u hu v hv huv hgap (Sum.inr i)

end PaperI
