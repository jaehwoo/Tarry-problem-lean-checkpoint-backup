import PaperILean.SignedPlanarCenterlineFormat
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! I1263: exact Euclidean transverse displacement and containment for the
same signed-coordinate centerline. The closed transverse interval requires a
strict margin below the distance buffer. Empty, singleton, and stationary
pieces are allowed. No preparation, positive area, or band construction is
asserted by these pointwise geometric lemmas. -/

noncomputable section
namespace PaperI
open Set

/-- The transverse displacement of the existing signed-coordinate graph. -/
def signedPlanarStripPoint (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (q u : ℝ) :
    WithLp 2 (Fin 2 → ℝ) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm (signedPlanarDecode i σ ![q, h q + u])

/-- A closed transverse strip over an arbitrary longitudinal subset. -/
def signedPlanarStrip (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (J : Set ℝ) (w : ℝ) :
    Set (WithLp 2 (Fin 2 → ℝ)) :=
  {p | ∃ q ∈ J, ∃ u : ℝ, |u| ≤ w ∧ p = signedPlanarStripPoint i σ h q u}

theorem signedPlanarStripPoint_dist (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (q u : ℝ) :
    dist (signedPlanarStripPoint i σ h q u) (signedPlanarStripPoint i σ h q 0) = |u| := by
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two]
  fin_cases i <;>
    simp [signedPlanarStripPoint, signedPlanarDecode, Real.dist_eq, Real.sqrt_sq_eq_abs]

theorem signedPlanarStrip_empty (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ) (w : ℝ) :
    signedPlanarStrip i σ h ∅ w = ∅ := by
  ext p
  simp [signedPlanarStrip]

theorem signedPlanarStrip_of_neg (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ)
    (J : Set ℝ) {w : ℝ} (hw : w < 0) : signedPlanarStrip i σ h J w = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro p ⟨q,hq,u,hu,rfl⟩
  exact (not_le_of_gt hw) ((abs_nonneg u).trans hu)

theorem signedPlanarStrip_mono_domain (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ)
    {J K : Set ℝ} (hJK : J ⊆ K) (w : ℝ) :
    signedPlanarStrip i σ h J w ⊆ signedPlanarStrip i σ h K w := by
  rintro p ⟨q,hq,u,hu,rfl⟩
  exact ⟨q,hJK hq,u,hu,rfl⟩

theorem signedPlanarStrip_subset_of_buffer
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (i : Fin 2) (σ : ℝ) (h : ℝ → ℝ)
    (J : Set ℝ) (r w : ℝ) (hw : w < r)
    (hbuffer : ∀ q ∈ J, r ≤ Metric.infDist (signedPlanarStripPoint i σ h q 0) Eᶜ) :
    signedPlanarStrip i σ h J w ⊆ E := by
  rintro p ⟨q,hq,u,hu,rfl⟩
  apply Metric.ball_infDist_compl_subset (s := E)
  rw [Metric.mem_ball, signedPlanarStripPoint_dist]
  exact (hu.trans_lt hw).trans_le (hbuffer q hq)

theorem signedPlanarStripPoint_zero_eq_path
    (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) (i k : Fin 2) (hik : i ≠ k)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ)
    (he : ∀ t ∈ Icc a b, h (σ*γ t i)=γ t k)
    (ho : ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q)
    {q : ℝ} (hq : q ∈ Icc (σ*γ a i) (σ*γ b i)) :
    ∃ t ∈ Icc a b, signedPlanarStripPoint i σ h q 0 =
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t) := by
  obtain ⟨t,ht,hqt⟩ := ho q hq
  refine ⟨t,ht,?_⟩
  apply congrArg (WithLp.equiv 2 (Fin 2 → ℝ)).symm
  apply (signedPlanarDecode_eq_iff i k hik σ hσ _ (γ t)).mpr
  constructor
  · simpa using hqt.symm
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, add_zero, ← hqt] using he t ht

theorem signedPlanarStrip_subset_of_path_buffer
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (γ : ℝ → Fin 2 → ℝ) (a b : ℝ)
    (i k : Fin 2) (hik : i ≠ k) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ)
    (he : ∀ t ∈ Icc a b, h (σ*γ t i)=γ t k)
    (ho : ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q)
    (r w : ℝ) (hw : w < r)
    (hbuffer : ∀ t ∈ Icc a b,
      r ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) Eᶜ) :
    signedPlanarStrip i σ h (Icc (σ*γ a i) (σ*γ b i)) w ⊆ E := by
  apply signedPlanarStrip_subset_of_buffer E i σ h _ r w hw
  intro q hq
  obtain ⟨t,ht,hpoint⟩ := signedPlanarStripPoint_zero_eq_path γ a b i k hik σ hσ h he ho hq
  rw [hpoint]
  exact hbuffer t ht

theorem signedPlanarStrip_subset_of_half_width_buffer
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (γ : ℝ → Fin 2 → ℝ) (a b : ℝ)
    (i k : Fin 2) (hik : i ≠ k) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (h : ℝ → ℝ)
    (he : ∀ t ∈ Icc a b, h (σ*γ t i)=γ t k)
    (ho : ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q)
    (W : ℝ) (hW : 0 < W)
    (hbuffer : ∀ t ∈ Icc a b,
      W/2 ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t)) Eᶜ) :
    signedPlanarStrip i σ h (Icc (σ*γ a i) (σ*γ b i)) (W/4) ⊆ E := by
  exact signedPlanarStrip_subset_of_path_buffer E γ a b i k hik σ hσ h he ho
    (W/2) (W/4) (by linarith) hbuffer

end PaperI
