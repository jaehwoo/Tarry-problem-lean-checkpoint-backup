import PaperILean.BufferedFormattedPlanarArcs
import PaperILean.PreparedCenterlineInterval

/-! I1263: preparation of the same buffered graph witness. Reconstructed from
the saved checkpoint128 progress and its recorded mathematical specification;
the unsaved final checkpoint128 source bytes are not claimed to be recovered.
No area, distance-band construction, packing or assignment is assumed here. -/

noncomputable section
namespace PaperI
open Set

def PreparedBufferedSpanningPlanarGraphArc (γ : ℝ → Fin 2 → ℝ)
    (a b R Cspan : ℝ) (s D : ℕ) (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ)
    (N : ℕ) (Cprep : ℝ) (Kprep : ℕ) : Prop :=
  ∃ i k : Fin 2, i ≠ k ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
    MonotoneOn (fun t => σ*γ t i) (Icc a b) ∧
    R ≤ Cspan*(σ*γ b i-σ*γ a i) ∧ ∃ h : ℝ → ℝ,
    LipschitzOnWith 1 h (Icc (σ*γ a i) (σ*γ b i)) ∧
    (∀ t ∈ Icc a b, h (σ*γ t i)=γ t k) ∧
    (∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q) ∧
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ s ∧
      (∀ p ∈ B, p.totalDegree ≤ D) ∧
      PolynomialSignDetermined B (signedPlanarCenterlineGraph γ a b i σ h) ∧
      (∀ J : Set ℝ, J ⊆ Icc (σ*γ a i) (σ*γ b i) →
        signedPlanarStrip i σ h J (W/4) ⊆ E) ∧
      ∃ u v : ℝ, u < v ∧ Icc u v ⊆ Icc (σ*γ a i) (σ*γ b i) ∧
        (σ*γ b i-σ*γ a i)/(Kprep : ℝ) ≤ v-u ∧
        R ≤ Cspan*(Kprep : ℝ)*(v-u) ∧ AnalyticOnNhd ℝ h (Icc u v) ∧
        (∀ x ∈ Icc u v, ∀ n ≤ N,
          |iteratedDeriv n (fun q => h q-h (σ*γ a i)) x| ≤
            Cprep*(σ*γ b i-σ*γ a i)/(σ*γ b i-σ*γ a i)^n) ∧
        (∀ x ∈ Icc u v, ∀ n, 0 < n → n ≤ N →
          |iteratedDeriv n h x| ≤ Cprep*(σ*γ b i-σ*γ a i)/(σ*γ b i-σ*γ a i)^n) ∧
        signedPlanarStrip i σ h (Icc u v) (W/4) ⊆ E

theorem preparedBufferedSpanningPlanarGraphArc_forget
    {γ : ℝ → Fin 2 → ℝ} {a b R Cspan W Cprep : ℝ} {s D N Kprep : ℕ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (h : PreparedBufferedSpanningPlanarGraphArc γ a b R Cspan s D E W N Cprep Kprep) :
    BufferedFormattedSpanningPlanarGraphArc γ a b R Cspan s D E W := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,_⟩ := h
  exact ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer⟩

theorem published_buffered_formatted_arc_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPiece : PublishedPiecewiseNashExtensions) (s D N : ℕ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧ ∃ Kprep : ℕ, 0 < Kprep ∧
      ∀ (γ : ℝ → Fin 2 → ℝ) (a b R Cspan : ℝ)
        (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ),
      0 < R → 0 ≤ Cspan →
      BufferedFormattedSpanningPlanarGraphArc γ a b R Cspan s D E W →
      PreparedBufferedSpanningPlanarGraphArc γ a b R Cspan s D E W N Cprep Kprep := by
  obtain ⟨C,hC,K,hK,hprepare⟩ := published_bounded_format_lipschitz_prepared_interval
    hDD hCell hHardt hQE hPiece s D N
  refine ⟨C,hC,K,hK,?_⟩
  intro γ a b R Cspan E W hR hCspan harc
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer⟩ := harc
  have hpos : 0 < σ*γ b i-σ*γ a i := by
    by_contra hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos hCspan (le_of_not_gt hn)
    linarith
  obtain ⟨u,v,huv,hsub,hlen,hA,hcenter,hderiv⟩ := hprepare B
    (signedPlanarCenterlineGraph γ a b i σ h) hBc hBd hB h
    (σ*γ a i) (σ*γ b i) (sub_pos.mp hpos)
    (by
      intro x hx y
      simp only [signedPlanarCenterlineGraph,mem_setOf_eq,
        Matrix.cons_val_zero,Matrix.cons_val_one,hx,true_and]) hl
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hlong : σ*γ b i-σ*γ a i ≤ (K : ℝ)*(v-u) := by
    simpa only [mul_comm] using (div_le_iff₀ hKreal).mp hlen
  refine ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,?_,hA,hcenter,hderiv,hbuffer _ hsub⟩
  calc
    R ≤ Cspan*(σ*γ b i-σ*γ a i) := hs
    _ ≤ Cspan*((K : ℝ)*(v-u)) := mul_le_mul_of_nonneg_left hlong hCspan
    _ = Cspan*(K : ℝ)*(v-u) := by ring

theorem published_cylindrical_uniform_prepared_buffered_planar_arc
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hPiece : PublishedPiecewiseNashExtensions)
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (s D N : ℕ) :
    ∃ sPath dPath K sCenter dCenter : ℕ,
      ∃ Cprep : ℝ, 1 ≤ Cprep ∧ ∃ Kprep : ℕ, 0 < Kprep ∧
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' S) →
      ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ), 0 < W →
      (∀ x ∈ S, W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ) →
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ γ : SemialgebraicUnitPath S a b,
      ∃ P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0=0 ∧ t n=1 ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1))) ∧
      ∃ j < n, PreparedBufferedSpanningPlanarGraphArc γ.toFun (t j) (t (j+1))
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b)) (2*(K : ℝ))
        sCenter dCenter E W N Cprep Kprep := by
  obtain ⟨sPath,dPath,K,sCenter,dCenter,hpaths⟩ :=
    published_cylindrical_uniform_buffered_formatted_macroscopic_planar_arc
      hCAD hHardt hQQE hNash hCell hPiece s D
  obtain ⟨C,hC,Kprep,hKprep,hprep⟩ := published_buffered_formatted_arc_preparation
    hDD hCell hHardt.toHardtTriviality hQQE.toRealSemialgebraicity hPiece sCenter dCenter N
  refine ⟨sPath,dPath,K,sCenter,dCenter,C,hC,Kprep,hKprep,?_⟩
  intro A S hc hd hS hconn hbounded E W hW hbuffer a ha b hb hab
  obtain ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,hspan⟩ :=
    hpaths A S hc hd hS hconn hbounded E W hW hbuffer a ha b hb
  refine ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,?_⟩
  apply hprep γ.toFun (t j) (t (j+1)) _ (2*(K : ℝ)) E W _ (by positivity) hspan
  apply dist_pos.mpr
  exact fun he => hab ((WithLp.equiv 2 (Fin 2 → ℝ)).symm.injective he)

end PaperI
