import PaperILean.OriginalPlanarArcDirections
import PaperILean.PlanarMacroscopicArc

/-! I654/I1263: subdivide ANY supplied bounded-format path by the original
analytic and actual derivative-sign cuts of x,y,x+y,x-y. No path is replaced.
The cut budget depends only on the path graph format, not the containing set.
This is pointwise data, not yet a measurable choice of cuts. -/
noncomputable section
namespace PaperI
open Set

theorem planarReadout_global_graph_format (i : Fin 4) :
    ∃ A : Finset (MvPolynomial (Fin 2 ⊕ Unit) ℝ), A.card ≤ 1 ∧
      (∀ q ∈ A, q.totalDegree ≤ 1) ∧
      PolynomialSignDetermined A (scalarFunctionGraph univ (planarReadout i)) := by
  simpa using planarReadout_graph_bounded_sign_format ∅ univ 0 0
    (by simp) (by simp) polynomialSignDetermined_univ i

theorem published_bounded_path_planar_readout_cuts
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (s d : ℕ) :
    ∃ K : ℕ, ∀ (S : Set (Fin 2 → ℝ)) (a b : Fin 2 → ℝ)
      (γ : SemialgebraicUnitPath S a b) (P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
      P.card ≤ s → (∀ q ∈ P, q.totalDegree ≤ d) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧
        (∀ c ∈ C, c ∈ Icc (0 : ℝ) 1) ∧ C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          ∀ i, AnalyticOnNhd ℝ (fun t => planarReadout i (γ.toFun t)) (Ioo u v) ∧
            DerivativeSignOn (fun t => planarReadout i (γ.toFun t)) (Ioo u v) := by
  obtain ⟨sc,dc,hcomp⟩ := published_bounded_scalar_composition_sign_format hQE (Fin 2) s d 1 1
  obtain ⟨K,hcuts⟩ := published_bounded_sign_format_original_common_subdivision
    hCell hHardt.toHardtTriviality hQE hNash hPiece (Fin 4) sc dc
  refine ⟨K,?_⟩
  intro S a b γ P hcard hdeg hP
  let γu : SemialgebraicUnitPath univ a b := γ.weaken (subset_univ S)
  apply hcuts (fun i t => planarReadout i (γ.toFun t)) 0 1 (by norm_num)
  · intro i
    exact (planarReadout_continuous i).comp_continuousOn γ.continuousOn
  · intro i
    obtain ⟨A,hAc,hAd,hA⟩ := planarReadout_global_graph_format i
    obtain ⟨B,hBc,hBd,hB⟩ := hcomp P A (unitPathGraph γ.toFun)
      (scalarFunctionGraph univ (planarReadout i)) hcard hdeg hP hAc hAd hA
    exact ⟨B,_,hBc,hBd,hB,scalarRelationComposition_unitPathGraph γu (planarReadout i)⟩

def OriginalPlanarGraphSubdivision (g : ℝ → Fin 2 → ℝ) (K : ℕ) : Prop :=
  ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧
    (∀ c ∈ C, c ∈ Icc (0 : ℝ) 1) ∧ C.card ≤ K ∧
    (∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      ∀ i, AnalyticOnNhd ℝ (fun r => planarReadout i (g r)) (Ioo u v) ∧
        DerivativeSignOn (fun r => planarReadout i (g r)) (Ioo u v)) ∧
    ∃ (n : ℕ) (t : ℕ → ℝ), n+1 ≤ K ∧ t 0 = 0 ∧ t n = 1 ∧
      MonotoneOn t (Icc 0 n) ∧
      ∀ j < n, t j ∈ C ∧ t (j+1) ∈ C ∧ t j < t (j+1) ∧
        (∀ c ∈ C, c ∉ Ioo (t j) (t (j+1))) ∧
        OriginalPlanarGraphArc g (t j) (t (j+1))

theorem published_bounded_path_original_graph_subdivision
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (s d : ℕ) :
    ∃ K : ℕ, ∀ (S : Set (Fin 2 → ℝ)) (a b : Fin 2 → ℝ)
      (γ : SemialgebraicUnitPath S a b) (P : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ)),
      P.card ≤ s → (∀ q ∈ P, q.totalDegree ≤ d) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      OriginalPlanarGraphSubdivision γ.toFun K := by
  obtain ⟨K,hK⟩ := published_bounded_path_planar_readout_cuts hCell hHardt hQE hNash hPiece s d
  refine ⟨K,?_⟩
  intro S a b γ P hcard hdeg hP
  obtain ⟨C,h0,h1,hC,hcardC,hcuts⟩ := hK S a b γ P hcard hdeg hP
  obtain ⟨n,t,hn,ht0,htn,ht,hgap⟩ := exists_sorted_cut_partition C h0 h1 hC
  refine ⟨C,h0,h1,hC,hcardC,hcuts,n,t,hn.trans_le hcardC,ht0,htn,ht,?_⟩
  intro j hj
  obtain ⟨hu,hv,huv,hgapj⟩ := hgap j hj
  have hlocal := hcuts (t j) hu (t (j+1)) hv huv hgapj
  have hsub : Icc (t j) (t (j+1)) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hC _ hu).1 (hC _ hv).2
  refine ⟨hu,hv,huv,hgapj,originalPlanarGraphArc_of_sum_sub_signs huv.le ?_ ?_ ?_ ?_⟩
  · intro k
    exact ((continuous_apply k).comp_continuousOn γ.continuousOn).mono hsub
  · intro k
    fin_cases k
    · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 0).1.differentiableOn
    · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 1).1.differentiableOn
  · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 2).2
  · simpa [planarReadout,planarReadoutPolynomial] using (hlocal 3).2

theorem OriginalPlanarGraphSubdivision.mono {g : ℝ → Fin 2 → ℝ} {K H : ℕ}
    (h : OriginalPlanarGraphSubdivision g K) (hKH : K ≤ H) :
    OriginalPlanarGraphSubdivision g H := by
  obtain ⟨C,h0,h1,hC,hcard,hcuts,n,t,hn,ht0,htn,ht,harc⟩ := h
  exact ⟨C,h0,h1,hC,hcard.trans hKH,hcuts,n,t,hn.trans hKH,ht0,htn,ht,harc⟩

theorem OriginalPlanarGraphSubdivision.budget_two_le {g : ℝ → Fin 2 → ℝ} {K : ℕ}
    (h : OriginalPlanarGraphSubdivision g K) : 2 ≤ K := by
  obtain ⟨C,h0,h1,hC,hcard,hcuts,n,t,hn,ht0,htn,ht,harc⟩ := h
  have hnp : 0 < n := by
    by_contra hnot
    have hz : n=0 := Nat.eq_zero_of_not_pos hnot
    rw [hz,ht0] at htn
    norm_num at htn
  omega

def OriginalSpanningPlanarGraphArc (g : ℝ → Fin 2 → ℝ) (a b R C : ℝ) : Prop :=
  ∃ (i k : Fin 2) (σ : ℝ), DirectedPlanarGraphArc g a b i k σ ∧
    (∀ t ∈ Ioo a b, |deriv (fun r => g r k) t| ≤ σ * deriv (fun r => g r i) t) ∧
    R ≤ C*(σ*g b i-σ*g a i)

theorem OriginalSpanningPlanarGraphArc.to_original {g : ℝ → Fin 2 → ℝ} {a b R C : ℝ}
    (h : OriginalSpanningPlanarGraphArc g a b R C) : OriginalPlanarGraphArc g a b := by
  obtain ⟨i,k,σ,hg,hcone,_⟩ := h
  exact ⟨i,k,σ,hg,hcone⟩

theorem OriginalSpanningPlanarGraphArc.to_spanning {g : ℝ → Fin 2 → ℝ} {a b R C : ℝ}
    (h : OriginalSpanningPlanarGraphArc g a b R C) : SpanningPlanarGraphArc g a b R C := by
  obtain ⟨i,k,σ,hg,hcone,hspan⟩ := h
  exact ⟨i,k,hg.1,σ,hg.2.1,hg.2.2.1,hspan,hg.2.2.2.2⟩

theorem OriginalSpanningPlanarGraphArc.mono_scale {g : ℝ → Fin 2 → ℝ} {a b R C D : ℝ}
    (h : OriginalSpanningPlanarGraphArc g a b R C) (hab : a ≤ b) (hCD : C ≤ D) :
    OriginalSpanningPlanarGraphArc g a b R D := by
  obtain ⟨i,k,σ,hg,hcone,hspan⟩ := h
  have hw : 0 ≤ σ*g b i-σ*g a i :=
    sub_nonneg.mpr (hg.2.2.1 ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)
  exact ⟨i,k,σ,hg,hcone,hspan.trans (mul_le_mul_of_nonneg_right hCD hw)⟩

theorem OriginalSpanningPlanarGraphArc.positive_longitudinal_span
    {g : ℝ → Fin 2 → ℝ} {a b R C : ℝ}
    (h : OriginalSpanningPlanarGraphArc g a b R C) (hR : 0 < R) (hC : 0 < C) :
    ∃ (i k : Fin 2) (σ : ℝ), DirectedPlanarGraphArc g a b i k σ ∧
      (∀ t ∈ Ioo a b, |deriv (fun r => g r k) t| ≤ σ * deriv (fun r => g r i) t) ∧
      R/C ≤ σ*g b i-σ*g a i ∧ 0 < σ*g b i-σ*g a i := by
  obtain ⟨i,k,σ,hg,hcone,hspan⟩ := h
  have hb : R/C ≤ σ*g b i-σ*g a i :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hspan)
  exact ⟨i,k,σ,hg,hcone,hb,(div_pos hR hC).trans_le hb⟩

theorem OriginalSpanningPlanarGraphArc.tangent_projection
    {g : ℝ → Fin 2 → ℝ} {a b R C : ℝ}
    (h : OriginalSpanningPlanarGraphArc g a b R C) :
    ∃ (i k : Fin 2) (σ : ℝ), DirectedPlanarGraphArc g a b i k σ ∧
      R ≤ C*(σ*g b i-σ*g a i) ∧
      ∀ t ∈ Ioo a b,
        0 < (deriv (fun r => g r i) t)^2 + (deriv (fun r => g r k) t)^2 →
        (1/2:ℝ) ≤ σ * deriv (fun r => g r i) t /
          Real.sqrt ((deriv (fun r => g r i) t)^2 + (deriv (fun r => g r k) t)^2) := by
  obtain ⟨i,k,σ,hg,hcone,hspan⟩ := h
  refine ⟨i,k,σ,hg,hspan,?_⟩
  intro t ht hspeed
  apply dominant_nonzero_normalized_projection_half
    (v := deriv (fun r => g r k) t) (Real.sqrt_pos.mpr hspeed)
  · rw [Real.sq_sqrt hspeed.le]
    rcases hg.2.1 with hσ | hσ <;> simp [hσ]
  · exact hcone t ht

theorem exists_macroscopic_original_planar_graph_piece
    (g : ℝ → Fin 2 → ℝ) (n : ℕ) (t : ℕ → ℝ) (hn : 0 < n)
    (ht : ∀ j < n, t j ≤ t (j+1))
    (harc : ∀ j < n, OriginalPlanarGraphArc g (t j) (t (j+1))) :
    ∃ j < n, OriginalSpanningPlanarGraphArc g (t j) (t (j+1))
      (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (t 0)))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (t n)))) (2*(n : ℝ)) := by
  classical
  have ha (j : Fin n) : OriginalPlanarGraphArc g (t j.val) (t (j.val+1)) := harc j.val j.isLt
  choose i k σ hg hcone using ha
  let L : Fin n → ℝ := fun j => |g (t (j.val+1)) (i j)-g (t j.val) (i j)|
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) L
    ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hend (c : Fin 2) : |g (t 0) c-g (t n) c| ≤ (n : ℝ)*L j := by
    have hb : ∀ {r : ℕ}, r < n → dist (g (t r) c) (g (t (r+1)) c) ≤ L j := by
      intro r hr
      have hu : t r ∈ Icc (t r) (t (r+1)) := ⟨le_rfl,ht r hr⟩
      have hv : t (r+1) ∈ Icc (t r) (t (r+1)) := ⟨ht r hr,le_rfl⟩
      have hd := (hg ⟨r,hr⟩).2.2.2.1 (t r) hu (t (r+1)) hv c
      have hd' : dist (g (t r) c) (g (t (r+1)) c) ≤ L ⟨r,hr⟩ := by
        simpa only [Real.dist_eq,L,abs_sub_comm] using hd
      exact hd'.trans (hmax ⟨r,hr⟩ (Finset.mem_univ _))
    simpa only [Real.dist_eq,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
      dist_le_range_sum_of_dist_le (f := fun r => g (t r) c) n hb
  have hdist := planar_euclidean_dist_le_coordinate_sum (g (t 0)) (g (t n))
  have hwidth : σ j*g (t (j.val+1)) (i j)-σ j*g (t j.val) (i j)=L j := by
    have hw := (hg j).2.2.1 ⟨le_rfl,ht j.val j.isLt⟩ ⟨ht j.val j.isLt,le_rfl⟩ (ht j.val j.isLt)
    have hnon : 0 ≤ σ j*g (t (j.val+1)) (i j)-σ j*g (t j.val) (i j) := sub_nonneg.mpr hw
    rw [← abs_of_nonneg hnon]
    rcases (hg j).2.1 with hs | hs
    · simp only [hs,one_mul,L]
    · simp only [hs,neg_one_mul,neg_sub_neg,L,abs_sub_comm]
  refine ⟨j.val,j.isLt,i j,k j,σ j,hg j,hcone j,?_⟩
  rw [hwidth]
  linarith [hend 0,hend 1]

theorem OriginalPlanarGraphSubdivision.macroscopic_arc {g : ℝ → Fin 2 → ℝ} {K : ℕ}
    (h : OriginalPlanarGraphSubdivision g K) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1, u < v ∧
      OriginalSpanningPlanarGraphArc g u v
        (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 0))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 1))) (2*(K:ℝ)) := by
  obtain ⟨C,h0,h1,hC,hcard,hcuts,n,t,hn,ht0,htn,ht,harc⟩ := h
  have hnp : 0 < n := by
    by_contra hnot
    have hz : n=0 := Nat.eq_zero_of_not_pos hnot
    rw [hz,ht0] at htn
    norm_num at htn
  obtain ⟨j,hj,hspan⟩ := exists_macroscopic_original_planar_graph_piece g n t hnp
    (fun j hj => (harc j hj).2.2.1.le)
    (fun j hj => (harc j hj).2.2.2.2)
  have hscale : 2*(n:ℝ) ≤ 2*(K:ℝ) := by
    have hnk : n ≤ K := (Nat.le_succ n).trans hn
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnk) (by norm_num)
  refine ⟨t j,hC _ (harc j hj).1,t (j+1),hC _ (harc j hj).2.1,
    (harc j hj).2.2.1,?_⟩
  simpa only [ht0,htn] using
    hspan.mono_scale (harc j hj).2.2.1.le hscale

theorem OriginalPlanarGraphSubdivision.arc_of_half_separation
    {g : ℝ → Fin 2 → ℝ} {K : ℕ} {R : ℝ}
    (h : OriginalPlanarGraphSubdivision g K)
    (hsep : R/2 < dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 0))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 1))) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1, u < v ∧
      OriginalSpanningPlanarGraphArc g u v R (4*(K:ℝ)) := by
  obtain ⟨u,hu,v,hv,huv,i,k,σ,hg,hcone,hspan⟩ := h.macroscopic_arc
  refine ⟨u,hu,v,hv,huv,i,k,σ,hg,hcone,?_⟩
  linarith

end PaperI
