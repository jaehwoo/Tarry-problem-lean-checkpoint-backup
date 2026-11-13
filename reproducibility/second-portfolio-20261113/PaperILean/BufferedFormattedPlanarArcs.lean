import PaperILean.OriginalRouteFormattedPlanarArcs
import PaperILean.PlanarTransverseStrips

/-! I1263: attach transverse containment to the same original-route formatted
macroscopic arc. Every later restriction of its longitudinal interval retains
containment. Actual band construction, separated endpoints, derivative
preparation, area, packing and joint assignments remain separate obligations. -/

noncomputable section
namespace PaperI
open Set

def BufferedFormattedSpanningPlanarGraphArc (γ : ℝ → Fin 2 → ℝ)
    (a b R C : ℝ) (s D : ℕ) (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) : Prop :=
  ∃ i k : Fin 2, i ≠ k ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
    MonotoneOn (fun t => σ*γ t i) (Icc a b) ∧
    R ≤ C*(σ*γ b i-σ*γ a i) ∧ ∃ h : ℝ → ℝ,
    LipschitzOnWith 1 h (Icc (σ*γ a i) (σ*γ b i)) ∧
    (∀ t ∈ Icc a b, h (σ*γ t i)=γ t k) ∧
    (∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q) ∧
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ s ∧
      (∀ p ∈ B, p.totalDegree ≤ D) ∧
      PolynomialSignDetermined B (signedPlanarCenterlineGraph γ a b i σ h) ∧
      ∀ J : Set ℝ, J ⊆ Icc (σ*γ a i) (σ*γ b i) →
        signedPlanarStrip i σ h J (W/4) ⊆ E

theorem bufferedFormattedSpanningPlanarGraphArc_forget
    {γ : ℝ → Fin 2 → ℝ} {a b R C W : ℝ} {s D : ℕ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (h : BufferedFormattedSpanningPlanarGraphArc γ a b R C s D E W) :
    FormattedSpanningPlanarGraphArc γ a b R C s D := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,_⟩ := h
  exact ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB⟩

theorem formattedSpanningPlanarGraphArc_buffered
    {γ : ℝ → Fin 2 → ℝ} {a b R C : ℝ} {s D : ℕ}
    (harc : FormattedSpanningPlanarGraphArc γ a b R C s D)
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (hW : 0 < W)
    (hbuffer : ∀ t ∈ Icc a b,
      W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) Eᶜ) :
    BufferedFormattedSpanningPlanarGraphArc γ a b R C s D E W := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB⟩ := harc
  refine ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,?_⟩
  intro J hJ
  exact (signedPlanarStrip_mono_domain i σ h hJ (W/4)).trans
    (signedPlanarStrip_subset_of_half_width_buffer E γ a b i k hik σ hσ h he ho W hW hbuffer)

theorem published_cylindrical_uniform_buffered_formatted_macroscopic_planar_arc
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hPiece : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ sPath dPath K sCenter dCenter : ℕ,
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S) →
      ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ), 0 < W →
      (∀ x ∈ S, W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ) →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0=0 ∧ t n=1 ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1))) ∧
      ∃ j < n, BufferedFormattedSpanningPlanarGraphArc γ.toFun (t j) (t (j+1))
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b)) (2*(K : ℝ)) sCenter dCenter E W := by
  obtain ⟨sPath,dPath,K,sCenter,dCenter,hPaths⟩ :=
    published_cylindrical_uniform_formatted_macroscopic_planar_arc
      hCAD hHardt hQQE hNash hCell hPiece s D
  refine ⟨sPath,dPath,K,sCenter,dCenter,?_⟩
  intro A S hc hd hS hconn hbounded E W hW hbuffer a ha b hb
  obtain ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harc,j,hj,hspan⟩ :=
    hPaths A S hc hd hS hconn hbounded a ha b hb
  have ha' : 0 ≤ t j := by
    rw [← ht0]
    exact ht ⟨le_rfl, Nat.zero_le n⟩ ⟨Nat.zero_le _, hj.le⟩ (Nat.zero_le _)
  have hb' : t (j+1) ≤ 1 := by
    rw [← htn]
    exact ht ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, le_rfl⟩ hj
  refine ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harc,j,hj,?_⟩
  apply formattedSpanningPlanarGraphArc_buffered hspan E W hW
  intro u hu
  exact hbuffer (γ.toFun u) (γ.mapsTo ⟨ha'.trans hu.1,hu.2.trans hb'⟩)

end PaperI
