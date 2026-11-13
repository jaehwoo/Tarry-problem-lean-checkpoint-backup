import PaperILean.SignedPlanarCenterlineFormat
import PaperILean.UniformMacroscopicPlanarArcs
import PaperILean.QuantitativeQEImpliesQualitative

/-! Original I1263 route: retain the CAD path and the same macroscopic signed
graph piece, and add the checked uniform centerline format for preparation.
This does not assert preparation, strip containment, area, or assignment. -/

noncomputable section
namespace PaperI
open Set

def FormattedSpanningPlanarGraphArc (γ : ℝ → Fin 2 → ℝ)
    (a b R C : ℝ) (s D : ℕ) : Prop :=
  ∃ i k : Fin 2, i ≠ k ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
    MonotoneOn (fun t => σ*γ t i) (Icc a b) ∧
    R ≤ C*(σ*γ b i-σ*γ a i) ∧ ∃ h : ℝ → ℝ,
    LipschitzOnWith 1 h (Icc (σ*γ a i) (σ*γ b i)) ∧
    (∀ t ∈ Icc a b, h (σ*γ t i)=γ t k) ∧
    (∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q) ∧
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ s ∧
      (∀ p ∈ B, p.totalDegree ≤ D) ∧
      PolynomialSignDetermined B (signedPlanarCenterlineGraph γ a b i σ h)

theorem formattedSpanningPlanarGraphArc_forget
    {γ : ℝ → Fin 2 → ℝ} {a b R C : ℝ} {s D : ℕ}
    (h : FormattedSpanningPlanarGraphArc γ a b R C s D) :
    SpanningPlanarGraphArc γ a b R C := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,_⟩ := h
  exact ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho⟩

theorem published_spanningPlanarGraphArc_uniform_format
    (hQQE : PublishedQuantitativeRealQE) (s D : ℕ) :
    ∃ sOut DOut : ℕ,
    ∀ (γ : ℝ → Fin 2 → ℝ) (A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
    A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) →
    PolynomialSignDetermined A (unitPathGraph γ) →
    ∀ (a b R C : ℝ), a ≤ b → 0 ≤ a → b ≤ 1 →
    SpanningPlanarGraphArc γ a b R C →
    FormattedSpanningPlanarGraphArc γ a b R C sOut DOut := by
  obtain ⟨sOut,DOut,hF⟩ := published_signedPlanarCenterline_uniform_format hQQE s D
  refine ⟨sOut,DOut,?_⟩
  intro γ A hc hd hG a b R C hab ha hb harc
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho⟩ := harc
  exact ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,
    hF γ A hc hd hG a b hab ha hb i k hik σ hσ h hm he ho⟩

theorem published_cylindrical_uniform_formatted_macroscopic_planar_arc
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
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
      ∃ P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0=0 ∧ t n=1 ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1))) ∧
      ∃ j < n, FormattedSpanningPlanarGraphArc γ.toFun (t j) (t (j+1))
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b)) (2*(K : ℝ)) sCenter dCenter := by
  obtain ⟨sPath,dPath,K,hPaths⟩ := published_cylindrical_uniform_macroscopic_planar_arc
    hCAD hHardt hQQE.toRealSemialgebraicity hNash hCell hPiece s D
  obtain ⟨sCenter,dCenter,hF⟩ := published_spanningPlanarGraphArc_uniform_format hQQE sPath dPath
  refine ⟨sPath,dPath,K,sCenter,dCenter,?_⟩
  intro A S hc hd hS hconn hbounded a ha b hb
  obtain ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harc,j,hj,hspan⟩ :=
    hPaths A S hc hd hS hconn hbounded a ha b hb
  have ha' : 0 ≤ t j := by
    rw [← ht0]
    exact ht ⟨le_rfl, Nat.zero_le n⟩ ⟨Nat.zero_le _, hj.le⟩ (Nat.zero_le _)
  have hb' : t (j+1) ≤ 1 := by
    rw [← htn]
    exact ht ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, le_rfl⟩ hj
  exact ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harc,j,hj,
    hF γ.toFun P hPc hPd hP (t j) (t (j+1)) _ _ (harc j hj).1.le ha' hb' hspan⟩

end PaperI
