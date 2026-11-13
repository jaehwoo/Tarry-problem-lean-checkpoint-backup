import PaperILean.OriginalNormalJetBounds
import PaperILean.RawJetUniformBounds
import PaperILean.TensorOperatorComparison
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! I1305: transfer actual original phase coefficients to normal-phase jets.
For each fixed degree and fixed bounded physical set, the constant precedes
all coefficient vectors, derivative orders, graph choices and base points. -/
set_option maxSynthPendingDepth 4
noncomputable section
namespace PaperI
open Filter
open scoped Topology ContDiff

theorem originalNormal_fderiv_norm_eq_iterated {d : ℕ} (f : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) :
    ‖fderiv ℝ f v‖ = ‖iteratedFDeriv ℝ 1 f v‖ := by
  calc
    _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ f) v‖ := (norm_iteratedFDeriv_zero).symm
    _ = _ := norm_iteratedFDeriv_fderiv

theorem originalNormal_second_norm_eq_iterated {d : ℕ} (f : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) v‖ = ‖iteratedFDeriv ℝ 2 f v‖ := by
  calc
    _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ f)) v‖ := (norm_iteratedFDeriv_zero).symm
    _ = _ := by rw [norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]

theorem originalNormal_third_norm_eq_iterated {d : ℕ} (f : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) v‖ = ‖iteratedFDeriv ℝ 3 f v‖ := by
  calc
    _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) v‖ := (norm_iteratedFDeriv_zero).symm
    _ = _ := by rw [norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]

theorem originalNormalPhase_iterated_norm_le {k : ℕ} (F : CoefficientSpace k)
    (n r : ℕ) (x : PhysicalSpace) :
    ‖iteratedFDeriv ℝ r (originalNormalPhase F n) x‖ ≤
      ‖iteratedFDeriv ℝ (n+r) (phase F) x‖ := by
  induction n generalizing r with
  | zero =>
    have he : originalNormalPhase F 0=phase F := by funext x; rfl
    rw [Nat.zero_add,he]
  | succ n ih =>
    have he : originalNormalPhase F (n+1)=(fun t => fderiv ℝ (originalNormalPhase F n) t ![1,0,0]) :=
      funext (fun t => (originalNormalPhase_dx F n t).symm)
    rw [he]
    have hn : (r : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl r
    have hd := norm_iteratedFDeriv_clm_apply_const (c := (![1,0,0] : Fin 3 → ℝ)) (x := x)
      ((originalNormalPhase_contDiff F n ∞).fderiv_right (by simp)).contDiffAt hn
    rw [originalNormal_norm_normal,abs_one,one_mul,norm_iteratedFDeriv_fderiv] at hd
    rw [show n+1+r=n+(r+1) by omega]
    exact hd.trans (ih (r+1))

theorem originalNormalPhase_uniform_jet_bound (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : CoefficientSpace k) (x : PhysicalSpace), x ∈ X →
      ∀ n r : ℕ, n+r ≤ k → ‖iteratedFDeriv ℝ r (originalNormalPhase F n) x‖ ≤
        C * coefficientEuclideanNorm F := by
  obtain ⟨C,hC,hb⟩ := rawJetHSNorm_uniform_bound k X hX
  refine ⟨3^k*C,one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hC,?_⟩
  intro F x hx n r hnr
  calc
    _ ≤ ‖iteratedFDeriv ℝ (n+r) (phase F) x‖ := originalNormalPhase_iterated_norm_le F n r x
    _ ≤ 3^(n+r) * tensorHSNorm (iteratedFDeriv ℝ (n+r) (phase F) x) := tensor_opNorm_le_HS _
    _ ≤ 3^k*(C*coefficientEuclideanNorm F) := by
      apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hnr) (hb F x hx (n+r) hnr)
      · exact tensorHSNorm_nonneg _
      · positivity
    _ = _ := by ring

theorem originalNormalPhase_graph_jet_bounds {k : ℕ}
    (M : ℝ) (hM : 1 ≤ M) (F : CoefficientSpace k) (n : ℕ)
    (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ) (hc : ContinuousAt c v)
    (hroot : ∀ᶠ t in 𝓝 v, originalNormalPhase F n (originalNormalLift c t)=0)
    (hk : originalNormalPhase F (n+1) (originalNormalLift c v) ≠ 0)
    (hki : |(originalNormalPhase F (n+1) (originalNormalLift c v))⁻¹| ≤ M)
    (hjets : ∀ r ∈ Finset.Icc 1 3,
      ‖iteratedFDeriv ℝ r (originalNormalPhase F n) (originalNormalLift c v)‖ ≤ M) :
    ‖fderiv ℝ c v‖ ≤ M^2 ∧ ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6 ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ 4*M^10 := by
  have hcs := originalNormalPhase_same_graph_smooth F n c v hc hroot hk
  have hc3 : ContDiffAt ℝ 3 c v := hcs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  apply originalNormal_jet_norm_bounds M hM (originalNormalPhase F n) c v
    (originalNormalPhase_contDiff F n 3).contDiffAt hc3 hroot
  · rwa [originalNormalPhase_dx]
  · rwa [originalNormalPhase_dx]
  · rw [originalNormal_fderiv_norm_eq_iterated]; exact hjets 1 (by decide)
  · rw [originalNormal_second_norm_eq_iterated]; exact hjets 2 (by decide)
  · rw [originalNormal_third_norm_eq_iterated]; exact hjets 3 (by decide)

theorem originalNormalPhase_coefficient_graph_bounds (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      C*coefficientEuclideanNorm F ≤ M → ∀ n : ℕ, n+3 ≤ k →
      ∀ (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ), ContinuousAt c v →
      originalNormalLift c v ∈ X →
      (∀ᶠ t in 𝓝 v, originalNormalPhase F n (originalNormalLift c t)=0) →
      originalNormalPhase F (n+1) (originalNormalLift c v) ≠ 0 →
      |(originalNormalPhase F (n+1) (originalNormalLift c v))⁻¹| ≤ M →
      ‖fderiv ℝ c v‖ ≤ M^2 ∧ ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6 ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ 4*M^10 := by
  obtain ⟨C,hC,hb⟩ := originalNormalPhase_uniform_jet_bound k X hX
  refine ⟨C,hC,?_⟩
  intro M hM F hF n hn c v hc hv hroot hk hki
  apply originalNormalPhase_graph_jet_bounds M hM F n c v hc hroot hk hki
  intro r hr
  have hr3 := (Finset.mem_Icc.mp hr).2
  exact (hb F _ hv n r (by omega)).trans hF

theorem originalNormalPhase_manuscript_coefficient_bounds (k : ℕ) (X : Set PhysicalSpace)
    (hX : Bornology.IsBounded X) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ F : CoefficientSpace k,
      C*coefficientEuclideanNorm F ≤ M → ∀ m : ℕ, 2 ≤ m → m ≤ k/2 →
      ∀ (c : (Fin 2 → ℝ) → ℝ) (v : Fin 2 → ℝ), ContinuousAt c v →
      originalNormalLift c v ∈ X →
      (∀ᶠ t in 𝓝 v, originalNormalPhase F (m-1) (originalNormalLift c t)=0) →
      originalNormalPhase F m (originalNormalLift c v) ≠ 0 →
      |(originalNormalPhase F m (originalNormalLift c v))⁻¹| ≤ M →
      ‖fderiv ℝ c v‖ ≤ M^2 ∧ ‖fderiv ℝ (fderiv ℝ c) v‖ ≤ M^6 ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) v‖ ≤ 4*M^10 := by
  obtain ⟨C,hC,hb⟩ := originalNormalPhase_coefficient_graph_bounds k X hX
  refine ⟨C,hC,?_⟩
  intro M hM F hF m hm hmk c v hc hv hroot hk hki
  have he : m-1+1=m := by omega
  apply hb M hM F hF (m-1) (by omega) c v hc hv hroot
  · simpa only [he] using hk
  · simpa only [he] using hki

end PaperI
