import PaperILean.CylindricalAnalyticPaths
import PaperILean.BoundedPathOriginalVariation

/-! I651/I654 through the original cell/curve-selection path construction.
The path is selected before all functions and range bounds. Uniform analytic
and actual derivative-sign subdivision is reused for this very same path.
Hardt remains an explicit input to the scalar counting/subdivision route,
but is absent from the endpoint-path construction. -/

noncomputable section
namespace PaperI
open Set

theorem published_cylindrical_paths_original_subdivision_variation
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hPiece : PublishedPiecewiseNashExtensions)
    (d : ℕ) (ι : Type) [Fintype ι] (sS dS sF dF : ℕ) :
    ∃ sPath dPath K M : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin d) ℝ)) (S : Set ((Fin d) → ℝ)),
      A.card ≤ sS → (∀ q ∈ A, q.totalDegree ≤ dS) →
      PolynomialSignDetermined A S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ P : Finset (MvPolynomial (Unit ⊕ (Fin d)) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      (∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0 : ℝ) 1) ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          AnalyticOnNhd ℝ γ.toFun (Ioo u v)) ∧
      ∀ (f : ι → ((Fin d) → ℝ) → ℝ) (B : ι → ℝ),
      (∀ i, ContinuousOn (f i) S) →
      (∀ i, ∃ F : Finset (MvPolynomial ((Fin d) ⊕ Unit) ℝ),
        F.card ≤ sF ∧ (∀ q ∈ F, q.totalDegree ≤ dF) ∧
          PolynomialSignDetermined F (scalarFunctionGraph S (f i))) →
      (∀ i, ∀ x ∈ S, ∀ y ∈ S, |f i x - f i y| ≤ B i) →
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0 : ℝ) 1) ∧
        C.card ≤ K ∧
        (∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          ∀ i, AnalyticOnNhd ℝ (fun s => f i (γ.toFun s)) (Ioo u v) ∧
            DerivativeSignOn (fun s => f i (γ.toFun s)) (Ioo u v)) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = 0 ∧ t n = 1 ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, ∀ i, MonotoneOn (fun s => f i (γ.toFun s)) (Ioo (t j) (t (j + 1))) ∨
          AntitoneOn (fun s => f i (γ.toFun s)) (Ioo (t j) (t (j + 1)))) ∧
        ∀ i, BoundedVariationOn (fun s => f i (γ.toFun s)) (Icc (0 : ℝ) 1) ∧
          variationOnFromTo (fun s => f i (γ.toFun s)) univ 0 1 ≤ (M : ℝ) * B i := by
  obtain ⟨sPath, dPath, hPaths⟩ :=
    published_cylindrical_bounded_sign_format_piecewise_analytic_paths hCAD hQE hNash d sS dS
  obtain ⟨K, M, hM⟩ := published_bounded_unitPath_original_partition_variation
    hCell hHardt hQE hNash hPiece (Fin d) ι sPath dPath sF dF
  refine ⟨sPath, dPath, K, M, ?_⟩
  intro A S hAcard hAdegree hA hc a ha b hb
  obtain ⟨γ, P, hPcard, hPdegree, hP, hAnalytic⟩ :=
    hPaths A S hAcard hAdegree hA hc a ha b hb
  exact ⟨γ, P, hPcard, hPdegree, hP, hAnalytic,
    hM S a b γ P hPcard hPdegree hP⟩

end PaperI

