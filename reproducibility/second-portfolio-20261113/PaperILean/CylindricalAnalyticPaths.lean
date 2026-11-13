import PaperILean.CylindricalUniformEndpointPaths
import PaperILean.SemialgebraicPathAnalyticity

/-! I649: finite analytic cuts of the very same uniformly bounded CAD path.
The cut count is only asserted finite here; uniform function subdivisions
are obtained separately from the original derivative-sign argument. -/

noncomputable section
namespace PaperI

theorem published_cylindrical_bounded_sign_format_piecewise_analytic_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity) (n s D : ℕ) :
    ∃ sPath dPath : ℕ, ∀ (A : Finset (MvPolynomial (Fin n) ℝ)) (S : Set (Fin n → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
        ∃ B : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), B.card ≤ sPath ∧
          (∀ q ∈ B, q.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined B (unitPathGraph γ.toFun) ∧
        ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Set.Ioo u v) →
            AnalyticOnNhd ℝ γ.toFun (Set.Ioo u v) := by
  obtain ⟨sp,dp,h⟩ := published_cylindrical_bounded_sign_format_paths hCAD hQE n s D
  refine ⟨sp,dp,?_⟩
  intro A S hcard hdegree hS hc a ha b hb
  obtain ⟨γ,B,hB,hdeg,hGraph⟩ := h A S hcard hdegree hS hc a ha b hb
  exact ⟨γ,B,hB,hdeg,hGraph,γ.published_finite_analytic_cut_intervals hQE hNash⟩

end PaperI
