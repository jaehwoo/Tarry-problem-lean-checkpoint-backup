import PaperILean.BufferedBandSmallStrip
import PaperILean.AreaCertifiedPreparedPlanarArc

/-! I1259/I1263: apply the retained original path/subdivision and preparation
to endpoints chosen in the ACTUAL band component at scale max(W,diam C).
The component's bounded polynomial-sign description remains an explicit
application hypothesis. It is not supplied by a new external citation. -/

noncomputable section
namespace PaperI
open Set MeasureTheory

def bufferedBandCoordinates (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ)
    (z : WithLp 2 (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedBandComponent E W z

theorem bufferedBandCoordinates_isPreconnected
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (z : WithLp 2 (Fin 2 → ℝ)) :
    IsPreconnected (bufferedBandCoordinates E W z) := by
  exact (bufferedBandComponent_isPreconnected E W z).image _
    (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ)).continuousOn

theorem bufferedBandCoordinates_euclidean_image
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (z : WithLp 2 (Fin 2 → ℝ)) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' bufferedBandCoordinates E W z =
      bufferedBandComponent E W z := by
  simp [bufferedBandCoordinates,← image_comp]

theorem areaCertifiedPreparedPlanarArc_rescale
    {γ : ℝ → Fin 2 → ℝ} {a b R R' Cspan c W Cprep : ℝ} {s D N Kprep : ℕ}
    {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (hW : 0 ≤ W) (hCspan : 0 < Cspan) (hc : 0 < c) (hKprep : 0 < Kprep)
    (hR : R' ≤ c*R)
    (harc : AreaCertifiedPreparedPlanarArc γ a b R Cspan s D E W N Cprep Kprep) :
    AreaCertifiedPreparedPlanarArc γ a b R' (c*Cspan) s D E W N Cprep Kprep := by
  obtain ⟨i,k,hik,σ,hσ,hm,hs,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,hspan,hA,hcenter,hderiv,hinside⟩ :=
      areaCertifiedPreparedPlanarArc_forget harc
  apply preparedBufferedPlanarArc_area hW (mul_pos hc hCspan) hKprep
  refine ⟨i,k,hik,σ,hσ,hm,?_,h,hl,he,ho,B,hBc,hBd,hB,hbuffer,
    u,v,huv,hsub,hlen,?_,hA,hcenter,hderiv,hinside⟩
  · calc
      R' ≤ c*R := hR
      _ ≤ c*(Cspan*(σ*γ b i-σ*γ a i)) := mul_le_mul_of_nonneg_left hs hc.le
      _ = _ := by ring
  · calc
      R' ≤ c*R := hR
      _ ≤ c*(Cspan*(Kprep : ℝ)*(v-u)) := mul_le_mul_of_nonneg_left hspan hc.le
      _ = _ := by ring

theorem published_uniform_large_bufferedBand_prepared_arc
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQQE : PublishedQuantitativeRealQE)
    (hNash : PublishedOneVariableNashRegularity)
    (hCell : PublishedFiniteConnectedCover)
    (hPiece : PublishedPiecewiseNashExtensions)
    (hDD : PublishedEquispacedDividedDifferenceMeanValue) (s D N : ℕ) :
    ∃ sPath dPath K sCenter dCenter : ℕ,
      ∃ Cprep : ℝ, 1 ≤ Cprep ∧ ∃ Kprep : ℕ, 0 < Kprep ∧
      ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))), Bornology.IsBounded E →
      ∀ W : ℝ, 0 < W → ∀ z : WithLp 2 (Fin 2 → ℝ),
      W < Metric.diam (bufferedBandComponent E W z) →
      ∀ A : Finset (MvPolynomial (Fin 2) ℝ),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A (bufferedBandCoordinates E W z) →
      ∃ a ∈ bufferedBandComponent E W z, ∃ b ∈ bufferedBandComponent E W z,
      a ≠ b ∧ bufferedComponentScale E W z/2 < dist a b ∧
        dist a b ≤ bufferedComponentScale E W z ∧
      ∃ γ : SemialgebraicUnitPath (bufferedBandCoordinates E W z)
        ((WithLp.equiv 2 (Fin 2 → ℝ)) a) ((WithLp.equiv 2 (Fin 2 → ℝ)) b),
      ∃ P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), P.card ≤ sPath ∧
        (∀ q ∈ P, q.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined P (unitPathGraph γ.toFun) ∧
      ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0=0 ∧ t n=1 ∧
        MonotoneOn t (Icc 0 n) ∧
        (∀ j < n, t j < t (j+1) ∧ SignedPlanarGraphArc γ.toFun (t j) (t (j+1))) ∧
      ∃ j < n, AreaCertifiedPreparedPlanarArc γ.toFun (t j) (t (j+1))
        (bufferedComponentScale E W z) (4*(K : ℝ))
        sCenter dCenter E W N Cprep Kprep := by
  obtain ⟨sPath,dPath,K,sCenter,dCenter,Cprep,hCprep,Kprep,hKprep,hpaths⟩ :=
    published_cylindrical_uniform_area_certified_prepared_planar_arc
      hCAD hHardt hQQE hNash hCell hPiece hDD s D N
  refine ⟨sPath,dPath,K,sCenter,dCenter,Cprep,hCprep,Kprep,hKprep,?_⟩
  intro E hE W hW z hlarge A hAc hAd hA
  obtain ⟨a,ha,b,hb,hab,hsep,hdiam⟩ := bufferedBandComponent_large_endpoints hE hW z hlarge
  have hbounded : Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' bufferedBandCoordinates E W z) := by
    rw [bufferedBandCoordinates_euclidean_image]
    exact bufferedBandComponent_isBounded hE hW.le z
  have hbuffer : ∀ x ∈ bufferedBandCoordinates E W z,
      W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ := by
    rintro x ⟨y,hy,rfl⟩
    simpa only [Equiv.symm_apply_apply] using (bufferedBandComponent_buffer hy).1.le
  obtain ⟨γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,hcert⟩ :=
    hpaths A (bufferedBandCoordinates E W z) hAc hAd hA
      (bufferedBandCoordinates_isPreconnected E W z) hbounded E W hW hbuffer
      _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ (fun h => hab ((WithLp.equiv 2 _).injective h))
  refine ⟨a,ha,b,hb,hab,hsep,hdiam,γ,P,hPc,hPd,hP,n,t,hn,ht0,htn,ht,harcs,j,hj,?_⟩
  have hK : 0 < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_succ n) hn
  have hscaled := areaCertifiedPreparedPlanarArc_rescale (R' := bufferedComponentScale E W z)
    (c := 2) hW.le (by positivity) (by norm_num) hKprep (by simpa using (show
      bufferedComponentScale E W z ≤ 2*dist a b by linarith)) hcert
  convert hscaled using 1 <;> ring

end PaperI
