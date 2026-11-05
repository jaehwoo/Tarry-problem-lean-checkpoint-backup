import PaperILean.OriginalHaarWindowSubgroups
import PaperILean.OriginalHaarWindowPieces
import PaperILean.OriginalHaarOrbitBody

/-! Apply the original coefficient bound and physical pivot to the actual
quotient orbit along its chosen subgroup path. All derivative identities are
proved for that actual orbit; no desired chain-rule or pivot application is
retained as an additional project premise. -/
noncomputable section
namespace PaperI
open Set
open scoped BigOperators

private theorem originalHaar_body_continuousOn
    (g dg : ℝ → Fin 6 → ℝ) (S : Set ℝ)
    (hg : ContinuousOn g S) (hdg : ContinuousOn dg S) :
    ContinuousOn (fun t => originalAffineBodyCoordinates (g t) (dg t)) S := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i <;> dsimp [originalAffineBodyCoordinates] <;> fun_prop

/-- The endpoint increment for one actual analytic/sign piece. This includes
the exact phase-only physical pivot on the original subgroup Lie space. -/
theorem originalHaar_actual_analytic_piece_bound
    {k : ℕ} (K : OriginalHaarSubgroup) (F : CoefficientSpace k)
    (W : Set (CoefficientSpace k)) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hWnorm : ∀ J ∈ W, coefficientEuclideanNorm J ≤ B)
    (hWpiv : ∀ J ∈ W, ∀ v ∈ originalHaarSubgroupSet K,
      coordinateL2Norm v ≤ H*coefficientEuclideanNorm (originalHaarPhysicalLieAction J v))
    (g : ℝ → Fin 6 → ℝ) (hgc : ContinuousOn g (Icc (0:ℝ) 1))
    (hgW : ∀ s ∈ Icc (0:ℝ) 1, g s ∈ originalHaarOrbitWindow K F W)
    (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) (huv : u < v)
    (hgan : ∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => g t i) (Ioo u v))
    (hqan : ∀ α : MonomialIndex k,
      AnalyticOnNhd ℝ (fun t => originalUpperCoefficientPullback F (g t) α) (Ioo u v))
    (hqsign : ∀ α : MonomialIndex k,
      DerivativeSignOn (fun t => originalUpperCoefficientPullback F (g t) α) (Ioo u v)) :
    let L : ℝ := H*(Fintype.card (MonomialIndex k):ℝ)*(2*B)
    ‖originalUpperRelativeFrame (g u) (g v)‖ ≤ L*(1+L)^2 := by
  let q : MonomialIndex k → ℝ → ℝ := fun α t => originalUpperCoefficientPullback F (g t) α
  let dq : MonomialIndex k → ℝ → ℝ := fun α => deriv (q α)
  let b : ℝ → Fin 6 → ℝ := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
  have hsub : Icc u v ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
  have hsubopen : Ioo u v ⊆ Ioo (0:ℝ) 1 := fun t ht =>
    ⟨hu.1.trans_lt ht.1,ht.2.trans_le hv.2⟩
  have hga : AnalyticOnNhd ℝ g (Ioo u v) := AnalyticOnNhd.pi hgan
  have hgd (s : ℝ) (hs : s ∈ Ioo u v) : HasDerivAt g (deriv g s) s :=
    (hga s hs).differentiableAt.hasDerivAt
  have hqd (α : MonomialIndex k) (s : ℝ) (hs : s ∈ Ioo u v) :
      HasDerivAt (q α) (dq α s) s := (hqan α s hs).differentiableAt.hasDerivAt
  apply originalHaar_analytic_piece_relative_bound g b q dq u v B H huv hB hH
    (hgc.mono hsub)
  · exact originalHaar_body_continuousOn g (deriv g) _
      hga.continuousOn hga.deriv.continuousOn
  · intro s hs
    simpa only [b,originalUpperBodyVelocity_body] using hgd s hs
  · exact hqd
  · intro α
    exact (hqan α).deriv.continuousOn
  · exact hqsign
  · intro α s hs
    exact originalHaar_coefficient_coordinate_bound _ B
      (hWnorm _ (hgW s (hsub ⟨hs.1.le,hs.2.le⟩)).2) α
  · intro s hs i
    have hbodyK : b s ∈ originalHaarSubgroupSet K :=
      originalHaar_path_body_mem_subgroup K g (deriv g s) s (hsubopen hs)
        (hgd s hs) (fun t ht => (hgW t ht).1)
    have hactual : (fun α => dq α s) = originalHaarPhysicalLieAction
        (originalUpperCoefficientPullback F (g s)) (b s) := by
      have ho := OriginalHaarOrbitBody.orbit_hasDerivAt_body F g (deriv g s) s (hgd s hs)
      ext α
      exact (hqd α s hs).unique (hasDerivAt_pi.mp ho α)
    exact originalHaar_physical_pivot_body_majorant _ _ (b s) H hH
      (hWpiv _ (hgW s (hsub ⟨hs.1.le,hs.2.le⟩)).2 (b s) hbodyK) hactual i

end PaperI
