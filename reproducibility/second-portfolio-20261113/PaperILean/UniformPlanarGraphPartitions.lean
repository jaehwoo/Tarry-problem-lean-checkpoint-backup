import PaperILean.PlanarDerivativeCones
import PaperILean.PlanarLinearReadoutFormat
import PaperILean.CylindricalEndpointOriginalVariation

/-! I1263: the original actual-derivative-sign subdivision, applied to the four
fixed linear readouts, produces uniformly many signed coordinate graph pieces.
The constants precede the actual set and endpoints. Point images are retained.
The six published inputs are explicit; Hardt is used by scalar subdivision,
not by the cylindrical endpoint-path construction. -/

noncomputable section
namespace PaperI
open Set

theorem published_cylindrical_uniform_planar_graph_partition
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hPiece : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ sPath dPath K : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S) →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0=0 ∧ t n=1 ∧
        MonotoneOn t (Icc 0 n) ∧
        ∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1)) := by
  obtain ⟨sPath,dPath,K,M,hPaths⟩ :=
    published_cylindrical_paths_original_subdivision_variation
      hCAD hHardt hQE hNash hCell hPiece 2 (Fin 4) s D (s+1) (max D 1)
  refine ⟨sPath,dPath,K,?_⟩
  intro A S hcard hdegree hS hconn hbounded a ha b hb
  obtain ⟨γ,P,hPcard,hPdegree,hP,hAnalytic,hFunctions⟩ :=
    hPaths A S hcard hdegree hS hconn a ha b hb
  obtain ⟨C,h0,h1,hC,hCcard,hCuts,hRest⟩ :=
    hFunctions planarReadout
      (fun _ => 2*Metric.diam ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S))
      (fun i => (planarReadout_continuous i).continuousOn)
      (planarReadout_graph_bounded_sign_format A S s D hcard hdegree hS)
      (planarReadout_range_le_two_diameter S hbounded)
  obtain ⟨n,t,hn,ht0,htn,ht,hgap⟩ := exists_sorted_cut_partition C h0 h1 hC
  refine ⟨γ,P,hPcard,hPdegree,hP,n,t,hn.trans_le hCcard,ht0,htn,ht,?_⟩
  intro j hj
  obtain ⟨hu,hv,huv,hgapj⟩ := hgap j hj
  have hlocal := hCuts (t j) hu (t (j+1)) hv huv hgapj
  have hsub : Icc (t j) (t (j+1)) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hC _ hu).1 (hC _ hv).2
  refine ⟨huv,signedPlanarGraphArc_of_sum_sub_signs huv.le ?_ ?_ ?_ ?_⟩
  · intro k
    exact ((continuous_apply k).comp_continuousOn γ.continuousOn).mono hsub
  · intro k
    fin_cases k
    · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 0).1.differentiableOn
    · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 1).1.differentiableOn
  · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 2).2
  · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 3).2

end PaperI
