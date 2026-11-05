import PaperILean.PiecewiseOrderedIntegrals
import PaperILean.OriginalHaarWindowComponentPaths
import PaperILean.SectionIntegralReadouts
import PaperILean.FixedDFiberComponents
import PaperILean.OriginalGaussRelativeFrameIntegration
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! I3237[120,310): exact global ordered integrals on actual fixed-d paths.
The actual body field is constructed from the path derivative. Integrability
is proved, including singular endpoints and finite interior cuts. -/
noncomputable section
namespace PaperI.ActualOrderedPathStage
open Set MeasureTheory FinitePieceFTC PiecewiseOrderedIntegrals RegularSectionDifferential

/-- The actual path/body bridge, with no endpoint derivative assumptions. -/
theorem actual_body_on_pieces (g : ℝ → Fin 6 → ℝ) (C : Finset ℝ)
    (a z : ℝ) (haz : a ≤ z) (ha : a ∈ C) (hz : z ∈ C)
    (hC : ∀ c ∈ C, c ∈ Icc a z) (hc : ContinuousOn g (Icc a z))
    (hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      ∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => g t i) (Ioo u v) ∧
        DerivativeSignOn (fun t => g t i) (Ioo u v)) :
    let β := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
    (∀ i, IntervalIntegrable (fun t => β t i) volume a z) ∧
      originalUpperRelativeFrame (g a) (g z) = originalUpperOrderedSignature β a z := by
  let β := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
  have hgd (u : ℝ) (hu : u ∈ C) (v : ℝ) (hv : v ∈ C) (huv : u < v)
      (hno : ∀ c ∈ C, c ∉ Ioo u v) :
      ∀ t ∈ Ioo u v, HasDerivAt g (deriv g t) t := by
    have hga : AnalyticOnNhd ℝ g (Ioo u v) :=
      AnalyticOnNhd.pi (fun i => (hp u hu v hv huv hno i).1)
    exact fun t ht => (hga t ht).differentiableAt.hasDerivAt
  have hi (i : Fin 6) : IntervalIntegrable (fun t => deriv g t i) volume a z := by
    apply derivative_integrable_on_cut_pieces (fun t => g t i) _ C a z ha hz hC
      ((continuous_apply i).comp_continuousOn hc)
    intro u hu v hv huv hno
    exact ⟨fun t ht => hasDerivAt_pi.mp (hgd u hu v hv huv hno t ht) i,
      (hp u hu v hv huv hno i).2⟩
  have hb : ∀ i, IntervalIntegrable (fun t => β t i) volume a z :=
    body_integrable g (deriv g) a z (by simpa only [uIcc_of_le haz] using hc) hi
  refine ⟨hb,relative_ordered_integrals g β C a z haz hc hb ?_⟩
  intro t ht htC
  obtain ⟨u,hu,v,hv,huv,htuv,hno⟩ := point_in_cut_gap C ha hz ht htC
  simpa only [β,originalUpperBodyVelocity_body] using hgd u hu v hv huv hno t htuv

/-- A bounded-format actual fixed-d component path, with the original
augmented-coordinate analytic/sign subdivision retained. K is chosen before
all seed states, coefficients, fiber levels and endpoint choices. -/
theorem actual_fixed_d_ordered_integral_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ K : ℕ, ∀ (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      ∀ (d0 : ℝ) (z a b : Fin 6 → ℝ),
        a ∈ connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z →
        b ∈ connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z →
      ∃ γ : SemialgebraicUnitPath (connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z) a b,
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0:ℝ) 1) ∧ C.card ≤ K ∧
        (∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          (∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => γ.toFun t i) (Ioo u v) ∧
            DerivativeSignOn (fun t => γ.toFun t i) (Ioo u v)) ∧
          (∀ i : AugmentedCoordinateIndex k,
            AnalyticOnNhd ℝ (fun t => augmentedStateCoordinates k
              (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v) ∧
            DerivativeSignOn (fun t => augmentedStateCoordinates k
              (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v))) ∧
        (let β := fun t => originalAffineBodyCoordinates (γ.toFun t) (deriv γ.toFun t)
         (∀ i, IntervalIntegrable (fun t => β t i) volume 0 1) ∧
         (∀ i j, IntervalIntegrable (fun t => originalUpperIntegralOne β 0 t i * β t j) volume 0 1) ∧
         (∀ i j l, IntervalIntegrable (fun t => originalUpperIntegralTwo β 0 t i j * β t l) volume 0 1) ∧
         (originalAffineHomogeneousMatrix a)⁻¹ * originalAffineHomogeneousMatrix b =
           originalAffineHomogeneousMatrix (originalUpperOrderedSignature β 0 1) ∧
         originalUpperOrderedSignature β 0 1 3 = 0) := by
  obtain ⟨_N,K,hPaths⟩ := published_originalHaar_component_polynomial_paths
    hCell hPath hHardt hQE hNash hPiece (Fin 6) (Fin 6 ⊕ AugmentedCoordinateIndex k)
    (s+1) (max D 1) (max k 1)
  refine ⟨K,?_⟩
  intro S0 A E hAc hAd hAE d0 z a b ha hb
  obtain ⟨B,hBc,hBd,hBE⟩ :=
    FixedDFiberComponents.actual_d_fiber_sign_format A E s D hAc hAd hAE d0
  let Q : Fin 6 ⊕ AugmentedCoordinateIndex k → MvPolynomial (Fin 6) ℝ :=
    Sum.elim MvPolynomial.X (SectionIntegralReadouts.augmentedPolynomial S0)
  have hQ : ∀ i, (Q i).totalDegree ≤ max k 1 := by
    intro i
    cases i with
    | inl i => exact (by simp [Q] : (Q (Sum.inl i)).totalDegree ≤ 1).trans (Nat.le_max_right _ _)
    | inr i => exact SectionIntegralReadouts.augmentedPolynomial_degree S0 i
  obtain ⟨γ,C,hC0,hC1,hCI,hCK,hprops⟩ :=
    (hPaths B _ hBc hBd hBE).2.2 Q hQ z a b ha hb
  have hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      ∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => γ.toFun t i) (Ioo u v) ∧
        DerivativeSignOn (fun t => γ.toFun t i) (Ioo u v) := by
    intro u hu v hv huv hno i
    simpa only [Q,Sum.elim_inl,MvPolynomial.eval_X] using
      (hprops u hu v hv huv hno).2 (Sum.inl i)
  refine ⟨γ,C,hC0,hC1,hCI,hCK,?_,?_⟩
  · intro u hu v hv huv hno
    refine ⟨hp u hu v hv huv hno,?_⟩
    intro i
    simpa only [Q,Sum.elim_inr,SectionIntegralReadouts.augmentedPolynomial_eval] using
      (hprops u hu v hv huv hno).2 (Sum.inr i)
  · let β := fun t => originalAffineBodyCoordinates (γ.toFun t) (deriv γ.toFun t)
    obtain ⟨hbi,hformula⟩ := actual_body_on_pieces γ.toFun C 0 1 (by norm_num)
      hC0 hC1 hCI γ.continuousOn hp
    change originalUpperRelativeFrame (γ.toFun 0) (γ.toFun 1) =
      originalUpperOrderedSignature β 0 1 at hformula
    rw [γ.source,γ.target] at hformula
    obtain ⟨h2,h3⟩ := ordered_integrands_integrable β 0 1 hbi
    refine ⟨hbi,h2,h3,?_,?_⟩
    · rw [originalAffineHomogeneousMatrix_relative,hformula]
    · rw [← hformula]
      have had := ((connectedComponentIn_subset {g | g ∈ E ∧ g 3 = d0} z) ha).2
      have hbd := ((connectedComponentIn_subset {g | g ∈ E ∧ g 3 = d0} z) hb).2
      simp [originalUpperRelativeFrame,originalUpperAffineComp,originalUpperAffineInv,had,hbd]

end PaperI.ActualOrderedPathStage
