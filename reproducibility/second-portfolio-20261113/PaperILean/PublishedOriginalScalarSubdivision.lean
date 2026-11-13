import PaperILean.PublishedFormatAnalyticCuts
import PaperILean.PublishedFormatDerivativeSignCuts
import PaperILean.AnalyticSignCutRefinement

/-! The original I654 analytic/derivative-sign subdivision, with uniform
constants chosen before all coefficients, functions, endpoints and range
lengths. The qualitative Nash and semialgebraic inputs are explicit; every
uniform-cut construction and calculus application is checked locally. This
module does not assert the original cell/curve construction of the path.
Pre-strategy diagnostics: checkpoint108 records002,004,017,027. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem published_bounded_sign_format_analytic_derivative_cut_sets
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ P ∈ A, P.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          AnalyticOnNhd ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v) := by
  obtain ⟨KA,hKA⟩ := published_bounded_sign_format_analytic_cut_sets hCell hHardt hQE hPiece s D
  obtain ⟨KS,hKS⟩ := published_bounded_sign_format_derivative_sign_cut_sets hCell hHardt hQE hNash s D
  refine ⟨KA + KS,?_⟩
  intro A S hcard hdeg hS f a b hab hrep
  obtain ⟨CA,haA,hbA,hA,han,hcardA⟩ := hKA A S hcard hdeg hS f a b hab hrep
  obtain ⟨CS,haS,hbS,hSC,hcardS,hsgn⟩ := hKS A S hcard hdeg hS f a b hab hrep
  obtain ⟨C,ha,hb,hC,hbound,hprops⟩ := analytic_sign_cuts_union f CA CS
    haA hbA haS hbS hA hSC han (fun u hu v hv huv hgap => (hsgn u hu v hv huv hgap).2)
  exact ⟨C,ha,hb,hC,hbound.trans (Nat.add_le_add hcardA hcardS),hprops⟩

/-- One common cut set for the entire finite family. Continuity is retained
as in the manuscript; the stronger interior construction does not need it. -/
theorem published_bounded_sign_format_original_common_subdivision
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (ι : Type) [Fintype ι] (s D : ℕ) :
    ∃ K : ℕ, ∀ (f : ι → ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ P ∈ A, P.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f i t) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧
        C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          ∀ i, AnalyticOnNhd ℝ (f i) (Ioo u v) ∧ DerivativeSignOn (f i) (Ioo u v) := by
  classical
  obtain ⟨K,hK⟩ := published_bounded_sign_format_analytic_derivative_cut_sets
    hCell hHardt hQE hNash hPiece s D
  refine ⟨2 + ∑ _ : ι, K,?_⟩
  intro f a b hab _hf hgraph
  have hi (i : ι) : ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧
      (∀ c ∈ C, c ∈ Icc a b) ∧ C.card ≤ K ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        AnalyticOnNhd ℝ (f i) (Ioo u v) ∧ DerivativeSignOn (f i) (Ioo u v) := by
    obtain ⟨A,S,hcard,hdeg,hS,hrep⟩ := hgraph i
    exact hK A S hcard hdeg hS (f i) a b hab hrep
  choose cuts ha hb hcuts hcard hprops using hi
  exact common_analytic_sign_cut_set f cuts (fun _ => K) hab ha hb hcuts hcard hprops

/-- The same constructed analytic/sign cuts are sorted, the actual derivative
signs imply monotonicity, and the checked variation estimate uses the original
closed-interval continuity and range lengths. No monotonicity citation is used. -/
theorem published_bounded_sign_format_original_partition_variation
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (ι : Type) [Fintype ι] (s D : ℕ) :
    ∃ K M : ℕ, ∀ (f : ι → ℝ → ℝ) (a b : ℝ) (B : ι → ℝ), a ≤ b →
      (∀ i, ContinuousOn (f i) (Icc a b)) →
      (∀ i, ∃ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
        A.card ≤ s ∧ (∀ P ∈ A, P.totalDegree ≤ D) ∧ PolynomialSignDetermined A S ∧
        ∀ t ∈ Icc a b, ∀ y : ℝ, ![t,y] ∈ S ↔ y = f i t) →
      (∀ i, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f i x - f i y| ≤ B i) →
      ∃ C : Finset ℝ, a ∈ C ∧ b ∈ C ∧ (∀ c ∈ C, c ∈ Icc a b) ∧ C.card ≤ K ∧
        (∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          ∀ i, AnalyticOnNhd ℝ (f i) (Ioo u v) ∧ DerivativeSignOn (f i) (Ioo u v)) ∧
        ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ M ∧ t 0 = a ∧ t n = b ∧
          MonotoneOn t (Icc 0 n) ∧
          (∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
            AntitoneOn (f i) (Ioo (t j) (t (j + 1)))) ∧
          ∀ i, BoundedVariationOn (f i) (Icc a b) ∧
            variationOnFromTo (f i) univ a b ≤ (M : ℝ) * B i := by
  obtain ⟨K,hK⟩ := published_bounded_sign_format_original_common_subdivision
    hCell hHardt hQE hNash hPiece ι s D
  refine ⟨K,K,?_⟩
  intro f a b B hab hf hgraph hB
  obtain ⟨C,ha,hb,hC,hcard,hprops⟩ := hK f a b hab hf hgraph
  obtain ⟨n,t,hn,h0,hlast,ht,hgap⟩ := exists_sorted_cut_partition C ha hb hC
  have hnK : n ≤ K := by omega
  have hm : ∀ j < n, ∀ i, MonotoneOn (f i) (Ioo (t j) (t (j + 1))) ∨
      AntitoneOn (f i) (Ioo (t j) (t (j + 1))) := by
    intro j hj i
    obtain ⟨hu,hv,huv,hno⟩ := hgap j hj
    have hp := hprops (t j) hu (t (j + 1)) hv huv hno i
    exact monotoneOn_or_antitoneOn_of_derivative_sign hp.1.differentiableOn hp.2
  refine ⟨C,ha,hb,hC,hcard,hprops,n,t,hnK,h0,hlast,ht,hm,?_⟩
  have hv := family_variation_le_of_bounded_common_partition f B K t n hnK ht
    (by simpa only [h0,hlast] using hf) hm (by simpa only [h0,hlast] using hB)
  simpa only [h0,hlast] using hv

end PaperI
