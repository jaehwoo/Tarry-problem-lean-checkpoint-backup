import PaperILean.FrameCriticalMinimum
import PaperILean.ParameterImplicitFunction

/-! Smooth dependence in Lemma 2.3(i), I227,248, for fixed lambda>0.
Existence and uniqueness are previously checked; no minimizing selection is
assumed smooth. The actual local critical branch is proved globally minimizing.
The resulting Gram is independent of the chosen representative. -/
noncomputable section
open scoped Matrix Matrix.L2OpNorm Topology
namespace PaperI

def minimizingFrame {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (hlam : 0 < lam) : PositiveFrame :=
  ⟨(exists_FrameEnergy_minimum F c lam hlam.le).choose,
    (exists_FrameEnergy_minimum F c lam hlam.le).choose_spec.1.det_pos⟩

theorem minimizingFrame_is_minimum {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ D : PositiveFrame, FrameEnergy F c lam (minimizingFrame F c lam hlam).val ≤
      FrameEnergy F c lam D.val :=
  (exists_FrameEnergy_minimum F c lam hlam.le).choose_spec.2

def minimizingGram {k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (p : CoefficientSpace k × PhysicalSpace) : SymmetricMatrix 3 :=
  symmetricFrameGram (minimizingFrame p.1 p.2 lam hlam).val

theorem minimizingGram_posDef {k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (p : CoefficientSpace k × PhysicalSpace) : (minimizingGram lam hlam p).val.PosDef :=
  positiveFrame_gram_posDef _

theorem minimizingGram_eq_of_minimum {k : ℕ} (F : CoefficientSpace k) (c : PhysicalSpace)
    (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    minimizingGram lam hlam (F, c) = symmetricFrameGram B.val := by
  apply Subtype.ext
  exact FrameEnergy_minimizers_same_gram F c lam hlam (minimizingFrame F c lam hlam) B
    (minimizingFrame_is_minimum F c lam hlam) hB

theorem exists_analytic_minimizing_coordinates {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 < lam) (B : PositiveFrame)
    (hB : ∀ D : PositiveFrame, FrameEnergy F c lam B.val ≤ FrameEnergy F c lam D.val) :
    ∃ s : CoefficientSpace k × PhysicalSpace → SymmetricMatrix 3,
      s (F, c) = 0 ∧ ContDiffAt ℝ ⊤ s (F, c) ∧
        ∀ᶠ p in 𝓝 (F, c), ∀ D : PositiveFrame,
          FrameEnergy p.1 p.2 lam (symmetricFrameParam B (s p)) ≤ FrameEnergy p.1 p.2 lam D.val := by
  obtain ⟨s, hs, hsm, hz⟩ := exists_analytic_local_zero
    (symmetricFrameGradient (k := k) lam B) (contDiff_symmetricFrameGradient lam B) (F, c)
    (symmetricFrameGradient_zero_of_minimum F c lam B hB)
    (symmetricFrameEnergyHessianEquiv F c lam hlam B)
    (symmetricFrameGradient_frame_hasStrictFDerivAt F c lam hlam B).hasFDerivAt
  refine ⟨s, hs, hsm, hz.mono ?_⟩
  intro p hp
  exact FrameEnergy_minimum_of_coordinate_critical p.1 p.2 lam hlam B (s p) hp

theorem contDiffAt_minimizingGram {k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (p : CoefficientSpace k × PhysicalSpace) : ContDiffAt ℝ ⊤ (minimizingGram lam hlam) p := by
  let B := minimizingFrame p.1 p.2 lam hlam
  obtain ⟨s, hs, hsm, hmin⟩ := exists_analytic_minimizing_coordinates p.1 p.2 lam hlam B
    (minimizingFrame_is_minimum p.1 p.2 lam hlam)
  have hc : ContDiffAt ℝ ⊤ (fun q => symmetricGramCoordinates B (s q)) p :=
    (contDiff_symmetricGramCoordinates B).contDiffAt.comp p hsm
  apply hc.congr_of_eventuallyEq
  filter_upwards [hmin] with q hq
  rw [symmetricGramCoordinates_eq_frameGram]
  exact minimizingGram_eq_of_minimum q.1 q.2 lam hlam (positiveSymmetricFrame B (s q)) hq

theorem contDiff_minimizingGram {k : ℕ} (lam : ℝ) (hlam : 0 < lam) :
    ContDiff ℝ ⊤ (minimizingGram (k := k) lam hlam) :=
  contDiff_iff_contDiffAt.mpr (fun p => contDiffAt_minimizingGram lam hlam p)

theorem contDiff_infty_minimizingGram {k : ℕ} (lam : ℝ) (hlam : 0 < lam) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (minimizingGram (k := k) lam hlam) :=
  (contDiff_minimizingGram lam hlam).of_le le_top

theorem contDiff_infty_source_minimizingGram {k : ℕ} (CX C0 R : ℝ)
    (hCX : 2 ≤ CX) (hC0 : 2 ≤ C0) (hR : 2 ≤ R) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (minimizingGram (k := k) (sourceRegularization CX C0 R)
        (sourceRegularization_pos CX C0 R hCX hC0 hR)) :=
  contDiff_infty_minimizingGram _ _

end PaperI
