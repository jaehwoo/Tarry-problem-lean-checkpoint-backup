import PaperILean.PlanarMacroscopicArc

/-! Uniform graph-piece extraction for I1263 from the actual original-route
path. The same path and bounded-format graph are retained. The span estimate
is in Euclidean endpoint distance; no positive separation is assumed when
endpoints coincide. All six accepted inputs stay visible in the type. -/

noncomputable section
namespace PaperI
open Set

theorem published_cylindrical_uniform_macroscopic_planar_arc
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
        (∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1))) ∧
      ∃ j < n, SpanningPlanarGraphArc γ.toFun (t j) (t (j+1))
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b)) (2*(K : ℝ)) := by
  obtain ⟨sPath,dPath,K,hPaths⟩ := published_cylindrical_uniform_planar_graph_partition
    hCAD hHardt hQE hNash hCell hPiece s D
  refine ⟨sPath,dPath,K,?_⟩
  intro A S hcard hdegree hS hconn hbounded a ha b hb
  obtain ⟨γ,P,hPcard,hPdegree,hP,n,t,hn,ht0,htn,ht,harc⟩ :=
    hPaths A S hcard hdegree hS hconn hbounded a ha b hb
  have hnp : 0 < n := by
    by_contra hnot
    have hz : n=0 := Nat.eq_zero_of_not_pos hnot
    rw [hz,ht0] at htn
    norm_num at htn
  obtain ⟨j,hj,hspan⟩ := exists_macroscopic_planar_graph_piece γ.toFun n t hnp
    (fun j hj => (harc j hj).1.le) (fun j hj => (harc j hj).2)
  have hscale : 2*(n : ℝ) ≤ 2*(K : ℝ) := by
    have hnk : n ≤ K := (Nat.le_succ n).trans hn
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnk) (by norm_num)
  have hspan' := spanningPlanarGraphArc_mono_scale (harc j hj).1.le hscale hspan
  refine ⟨γ,P,hPcard,hPdegree,hP,n,t,hn,ht0,htn,ht,harc,j,hj,?_⟩
  simpa only [ht0,htn,γ.source,γ.target] using hspan'

end PaperI
