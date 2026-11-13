import PaperILean.SignedPlanarStripArea

/-! I1263: attach actual Euclidean area to the SAME prepared buffered graph.
The predicate retains every field of PreparedBufferedSpanningPlanarGraphArc;
the only additions are measurability, exact area and its macroscopic bound.
This does not construct distance bands or prove packing/endpoint estimates. -/

noncomputable section
namespace PaperI
open Set MeasureTheory

def AreaCertifiedPreparedPlanarArc (γ : ℝ → Fin 2 → ℝ)
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
        signedPlanarStrip i σ h (Icc u v) (W/4) ⊆ E ∧
        MeasurableSet (signedPlanarStrip i σ h (Icc u v) (W/4)) ∧
        volume.real (signedPlanarStrip i σ h (Icc u v) (W/4)) = (v-u)*W/2 ∧
        R*W/(2*Cspan*(Kprep : ℝ)) ≤
          volume.real (signedPlanarStrip i σ h (Icc u v) (W/4))

theorem areaCertifiedPreparedPlanarArc_forget
    {γ : ℝ → Fin 2 → ℝ} {a b R Cspan W Cprep : ℝ} {s D N Kprep : ℕ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (h : AreaCertifiedPreparedPlanarArc γ a b R Cspan s D E W N Cprep Kprep) :
    PreparedBufferedSpanningPlanarGraphArc γ a b R Cspan s D E W N Cprep Kprep := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,hspan,hA,hcenter,hderiv,hinside,_⟩ := h
  exact ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,hspan,hA,hcenter,hderiv,hinside⟩

theorem preparedBufferedPlanarArc_area
    {γ : ℝ → Fin 2 → ℝ} {a b R Cspan W Cprep : ℝ} {s D N Kprep : ℕ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hW : 0 ≤ W) (hCspan : 0 < Cspan) (hKprep : 0 < Kprep)
    (harc : PreparedBufferedSpanningPlanarGraphArc γ a b R Cspan s D E W N Cprep Kprep) :
    AreaCertifiedPreparedPlanarArc γ a b R Cspan s D E W N Cprep Kprep := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,hspan,hA,hcenter,hderiv,hinside⟩ := harc
  refine ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,hspan,hA,hcenter,hderiv,hinside,?_,?_,?_⟩
  · exact (signedPlanarStrip_measurable_volume i σ hσ h u v (W/4) hA.continuousOn).1
  · exact volume_real_signedPlanarStrip_quarter i σ hσ h u v W
      hA.continuousOn (le_of_lt huv) hW
  · exact signedPlanarStrip_area_lower_bound i σ hσ h u v W R Cspan Kprep
      hA.continuousOn (le_of_lt huv) hW hCspan hKprep hspan

theorem published_cylindrical_uniform_area_certified_prepared_planar_arc
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
      ∃ j < n, AreaCertifiedPreparedPlanarArc γ.toFun (t j) (t (j+1))
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b)) (2*(K : ℝ))
        sCenter dCenter E W N Cprep Kprep := by
  obtain ⟨sPath,dPath,K,sCenter,dCenter,C,hC,Kprep,hKprep,hpaths⟩ :=
    published_cylindrical_uniform_prepared_buffered_planar_arc
      hCAD hHardt hQQE hNash hCell hPiece hDD s D N
  refine ⟨sPath,dPath,K,sCenter,dCenter,C,hC,Kprep,hKprep,?_⟩
  intro A S hc hd hS hconn hbounded E W hW hbuffer a ha b hb hab
  obtain ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,hspan⟩ :=
    hpaths A S hc hd hS hconn hbounded E W hW hbuffer a ha b hb hab
  refine ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,?_⟩
  have hK : 0 < K := lt_of_lt_of_le (Nat.zero_lt_succ n) hn
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  exact preparedBufferedPlanarArc_area (le_of_lt hW) (by positivity) hKprep hspan

end PaperI
