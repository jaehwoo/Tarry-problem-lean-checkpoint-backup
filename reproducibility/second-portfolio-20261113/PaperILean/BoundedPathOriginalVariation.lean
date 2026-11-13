import PaperILean.CompatibleHardtForMonotonicity
import PaperILean.PublishedScalarCompositionFormat
import PaperILean.PublishedOriginalScalarSubdivision

/-! The original analytic and derivative-sign subdivision is applied to the
actual compositions along one bounded-format path. The actual bounded cut
witness is retained. Constants precede all coefficients, paths, functions and
range lengths. No monotonicity contract is used in this route. -/

noncomputable section
namespace PaperI
open Set

theorem published_bounded_unitPath_original_partition_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (κ ι : Type) [Fintype κ] [Fintype ι] (sPath dPath sF dF : ℕ) :
    ∃ K M : ℕ, ∀ (S : Set (κ → ℝ)) (a b : κ → ℝ)
      (γ : SemialgebraicUnitPath S a b) (P : Finset (MvPolynomial (Unit ⊕ κ) ℝ)),
      P.card ≤ sPath → (∀ q ∈ P, q.totalDegree ≤ dPath) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      ∀ (f : ι → (κ → ℝ) → ℝ) (B : ι → ℝ),
      (∀ i, ContinuousOn (f i) S) →
      (∀ i, ∃ A : Finset (MvPolynomial (κ ⊕ Unit) ℝ),
        A.card ≤ sF ∧ (∀ q ∈ A, q.totalDegree ≤ dF) ∧
          PolynomialSignDetermined A (scalarFunctionGraph S (f i))) →
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
  obtain ⟨sOut, dOut, hFormat⟩ :=
    published_bounded_scalar_composition_sign_format hQE κ sPath dPath sF dF
  obtain ⟨K, M, hM⟩ := published_bounded_sign_format_original_partition_variation
    hCell hHardt.toHardtTriviality hQE hNash hPiece ι sOut dOut
  refine ⟨K, M, ?_⟩
  intro S a b γ P hPcard hPdegree hP f B hf hF hB
  have hcont := fun i => γ.comp_continuousOn (f i) (hf i)
  have hrange := fun i => γ.comp_range_bound (f i) (B i) (hB i)
  have hgraph : ∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (G : Set (Fin 2 → ℝ)),
      A.card ≤ sOut ∧ (∀ q ∈ A, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined A G ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ y : ℝ, ![t,y] ∈ G ↔ y = f i (γ.toFun t) := by
    intro i
    obtain ⟨AF, hAFcard, hAFdegree, hAF⟩ := hF i
    obtain ⟨A, hAcard, hAdegree, hA⟩ := hFormat P AF
      (unitPathGraph γ.toFun) (scalarFunctionGraph S (f i))
      hPcard hPdegree hP hAFcard hAFdegree hAF
    exact ⟨A, scalarRelationComposition (unitPathGraph γ.toFun) (scalarFunctionGraph S (f i)),
      hAcard, hAdegree, hA, scalarRelationComposition_unitPathGraph γ (f i)⟩
  exact hM (fun i s => f i (γ.toFun s)) 0 1 B (by norm_num) hcont hgraph hrange

end PaperI
