import PaperILean.OriginalBivariatePolynomialJacobian

/-! I1283, original cited root-count argument. The source is Bafna--Sudan--
Velusamy--Xiang, arXiv:2102.00602v1, Definition 1.1 and Corollary 1.3.
The named proposition is the positive-degree, two-variable real instance of
that accepted published theorem, not a global axiom or a supplied inhabitant.
All degree and actual-polynomial/Jacobian substitutions are project proofs.
-/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

structure PublishedBivariateNonsingularBezout : Prop where
  bounded_roots : ∀ (P Q : MvPolynomial (Fin 2) ℝ) (d e : ℕ),
    0<d → 0<e → P.totalDegree≤d → Q.totalDegree≤e →
    ∃ s : Finset (Fin 2 → ℝ),
      (∀ w, w∈s ↔ MvPolynomial.eval w P=0 ∧ MvPolynomial.eval w Q=0 ∧
        (originalBivariateJacobian P Q w).det≠0) ∧ s.card≤d*e

def originalGaussRegularRootSet {k : ℕ} (F : CoefficientSpace k) (n : ℕ) (p z : ℝ) :
    Set (Fin 2 → ℝ) :=
  {w | originalNormalPhase F n ![w 0,w 1,z]=0 ∧
    fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,z] ![0,1,0]+
      p*fderiv ℝ (originalNormalPhase F n) ![w 0,w 1,z] ![1,0,0]=0 ∧
    (originalGaussRootJacobian (originalGaussPhaseSlice (originalNormalPhase F n) z) p w).det≠0}

theorem published_originalGauss_regular_root_count
    (cited : PublishedBivariateNonsingularBezout) {k : ℕ} (F : CoefficientSpace k) (m : ℕ)
    (hm : 2≤m) (hmk : m≤k/2) (p z : ℝ) :
    ∃ s : Finset (Fin 2 → ℝ),
      (∀ w, w∈s ↔ w∈originalGaussRegularRootSet F (m-1) p z) ∧
      s.card≤(k-m+1)*((k-m+1)-1) := by
  obtain ⟨hP,hQ⟩ := originalGauss_manuscript_slice_degrees F m hm hmk p z
  have hd : 0<k-m+1 := by omega
  have he : 0<(k-m+1)-1 := by omega
  obtain ⟨s,hs,hcard⟩ := cited.bounded_roots
    (originalGaussPolynomialSlice (originalNormalPolynomial F (m-1)) z)
    (originalGaussPolynomialSlice (originalGaussSecondPolynomial F (m-1) p) z)
    (k-m+1) ((k-m+1)-1) hd he hP hQ
  refine ⟨s,?_,hcard⟩
  intro w
  have hpair := originalGauss_polynomial_pair_eval F (m-1) p z w
  simpa only [originalGaussRegularRootSet,Set.mem_setOf_eq,hpair.1,hpair.2,
    originalGauss_polynomial_jacobian] using hs w

theorem originalNormal_graph_mem_regular_roots {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (c : (Fin 2 → ℝ) → ℝ) (y z : ℝ) (hc : ContDiffAt ℝ 2 c ![y,z])
    (hroot : ∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F n ![c w,w 0,w 1]=0)
    (hk : originalNormalPhase F (n+1) ![c ![y,z],y,z]≠0)
    (hr : fderiv ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] ![1,0]≠0) :
    ![c ![y,z],y]∈originalGaussRegularRootSet F n (fderiv ℝ c ![y,z] ![1,0]) z := by
  have hG := (originalNormalPhase_contDiff F n 2).contDiffAt (x := ![c ![y,z],y,z])
  refine ⟨hroot.self_of_nhds,originalNormal_graph_slope_equation _ c y z hG hc hroot,?_⟩
  rw [originalNormal_graph_gauss_jacobian_det _ c y z hG hc hroot,originalNormalPhase_dx]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hk)) hr

theorem published_originalGauss_retained_graph_count
    (cited : PublishedBivariateNonsingularBezout) {k : ℕ} (F : CoefficientSpace k) (m : ℕ)
    (hm : 2≤m) (hmk : m≤k/2) (p z : ℝ) :
    ∃ s : Finset (Fin 2 → ℝ), s.card≤(k-m+1)*((k-m+1)-1) ∧
      (∀ w, w∈s ↔ w∈originalGaussRegularRootSet F (m-1) p z) ∧
      ∀ (c : (Fin 2 → ℝ) → ℝ) (y : ℝ), ContDiffAt ℝ 2 c ![y,z] →
        (∀ᶠ w in 𝓝 (![y,z] : Fin 2 → ℝ), originalNormalPhase F (m-1) ![c w,w 0,w 1]=0) →
        originalNormalPhase F m ![c ![y,z],y,z]≠0 →
        fderiv ℝ (fun w => fderiv ℝ c w ![1,0]) ![y,z] ![1,0]≠0 →
        fderiv ℝ c ![y,z] ![1,0]=p → ![c ![y,z],y]∈s := by
  obtain ⟨s,hs,hcard⟩ := published_originalGauss_regular_root_count cited F m hm hmk p z
  refine ⟨s,hcard,hs,?_⟩
  intro c y hc hroot hk hr hp
  apply (hs _).mpr
  rw [← hp]
  apply originalNormal_graph_mem_regular_roots F (m-1) c y z hc hroot _ hr
  simpa only [show m-1+1=m by omega] using hk

end PaperI
