import PaperILean.FullFrameEnergyConvexity
import PaperILean.ExponentialFrameConnectivity
import PaperILean.FrameMinimumAttainment

/-! Uniqueness portion of Paper I Lemma 2.3(i), lines 227 and 248.
The minimum is the previously proved attained minimum, not an assumption of
the final existence-and-uniqueness theorem. Smooth dependence is separate. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm
namespace PaperI

theorem frameEnergyCurve_at_zero {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (B : PositiveFrame) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    frameEnergyCurve F c lam B H 0 = FrameEnergy F c lam B.val := by
  simp [frameEnergyCurve, NormedSpace.exp_zero]

theorem FrameEnergy_minimizers_same_gram {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B C : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val)
    (hC : ∀ D : PositiveFrame, FrameEnergy F c lam C.val ≤ FrameEnergy F c lam D.val) :
    B.val * B.valᵀ = C.val * C.valᵀ := by
  obtain ⟨H, hH, Q, hQ, hdet, hconn⟩ := exists_symmetric_exponential_connection B C
  by_contra hgram
  have hne : H ≠ 0 := by
    intro hz
    subst H
    exact hgram (same_gram_of_zero_exponential_connection B C Q hQ hconn)
  have hstrict := frameEnergyCurve_strictConvex F c lam hlam B H hH hne
  have he1 : frameEnergyCurve F c lam B H 1 = FrameEnergy F c lam C.val := by
    simp only [frameEnergyCurve, one_smul]
    rw [hconn, FrameEnergy_right_specialOrthogonal F c lam _ Q hQ hdet]
  have hmin0 : IsMinOn (frameEnergyCurve F c lam B H) Set.univ 0 := by
    intro t _
    rw [frameEnergyCurve_at_zero]
    exact hB (recenteredPositiveFrame B H hH t)
  have hmin1 : IsMinOn (frameEnergyCurve F c lam B H) Set.univ 1 := by
    intro t _
    rw [he1]
    exact hC (recenteredPositiveFrame B H hH t)
  have h01 : (0 : ℝ) = 1 := hstrict.eq_of_isMinOn hmin0 hmin1 (Set.mem_univ _) (Set.mem_univ _)
  norm_num at h01

theorem ellipsoidFrameEnergy_minimizers_unique {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (E D : PositiveFrameEllipsoid)
    (hE : ∀ T : PositiveFrameEllipsoid, ellipsoidFrameEnergy F c lam E ≤ ellipsoidFrameEnergy F c lam T)
    (hD : ∀ T : PositiveFrameEllipsoid, ellipsoidFrameEnergy F c lam D ≤ ellipsoidFrameEnergy F c lam T) :
    E = D := by
  induction E using Quotient.inductionOn with
  | h B =>
    induction D using Quotient.inductionOn with
    | h C =>
      apply Quotient.sound
      exact FrameEnergy_minimizers_same_gram F c lam hlam B C
        (fun T => hE (Quotient.mk positiveFrameGramSetoid T))
        (fun T => hD (Quotient.mk positiveFrameGramSetoid T))

theorem existsUnique_ellipsoidFrameEnergy_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) :
    ∃! E : PositiveFrameEllipsoid, ∀ D : PositiveFrameEllipsoid,
      ellipsoidFrameEnergy F c lam E ≤ ellipsoidFrameEnergy F c lam D := by
  obtain ⟨E, hE⟩ := exists_ellipsoidFrameEnergy_minimum F c lam hlam.le
  exact ⟨E, hE, fun D hD => ellipsoidFrameEnergy_minimizers_unique F c lam hlam D E hD hE⟩

theorem existsUnique_sourceEllipsoidFrameEnergy_minimum {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (CX C0 R : ℝ) (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    ∃! E : PositiveFrameEllipsoid, ∀ D : PositiveFrameEllipsoid,
      ellipsoidFrameEnergy F c (sourceRegularization CX C0 R) E ≤
        ellipsoidFrameEnergy F c (sourceRegularization CX C0 R) D :=
  existsUnique_ellipsoidFrameEnergy_minimum F c _ (sourceRegularization_pos CX C0 R hCX hC0 hR)

end PaperI
