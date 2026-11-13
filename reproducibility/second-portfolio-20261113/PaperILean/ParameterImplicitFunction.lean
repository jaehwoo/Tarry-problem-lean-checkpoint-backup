import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A parameter version of analytic IFT derived from the pinned inverse theorem.
The augmented map retains the parameter; its mixed derivative is not discarded.
No conclusion about global minima follows from this auxiliary theorem alone. -/
noncomputable section
open scoped Topology
namespace PaperI

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def parameterBlockEquiv (A : P →L[ℝ] V) (L : E ≃L[ℝ] V) : (P × E) ≃L[ℝ] (P × V) where
  toFun x := (x.1, A x.1 + L x.2)
  invFun y := (y.1, L.symm (y.2 - A y.1))
  map_add' := by intro x y; ext <;> simp [map_add, add_add_add_comm]
  map_smul' := by intro r x; ext <;> simp [map_smul, smul_add]
  left_inv := by intro x; simp
  right_inv := by intro y; simp
  continuous_toFun := continuous_fst.prodMk ((A.continuous.comp continuous_fst).add
    (L.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk (L.symm.continuous.comp
    (continuous_snd.sub (A.continuous.comp continuous_fst)))

theorem parameterBlockEquiv_apply (A : P →L[ℝ] V) (L : E ≃L[ℝ] V) (x : P × E) :
    parameterBlockEquiv A L x = (x.1, A x.1 + L x.2) := rfl

theorem parameterBlockEquiv_of_partial (D : P × E →L[ℝ] V) (L : E ≃L[ℝ] V)
    (hD : ∀ v : E, D (0, v) = L v) :
    (parameterBlockEquiv (D.comp (ContinuousLinearMap.inl ℝ P E)) L : P × E →L[ℝ] P × V) =
      (ContinuousLinearMap.fst ℝ P E).prod D := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · change D (x.1, 0) + L x.2 = D x
    rw [← hD, ← map_add]
    congr 1
    ext <;> simp

theorem exists_analytic_local_zero [CompleteSpace P] [CompleteSpace E]
    (g : P × E → V) (hg : ContDiff ℝ ⊤ g) (p : P)
    (hzero : g (p, 0) = 0) (L : E ≃L[ℝ] V)
    (hL : HasFDerivAt (fun S : E => g (p, S)) (L : E →L[ℝ] V) 0) :
    ∃ s : P → E, s p = 0 ∧ ContDiffAt ℝ ⊤ s p ∧
      ∀ᶠ q in 𝓝 p, g (q, s q) = 0 := by
  let D := fderiv ℝ g (p, 0)
  have hd : HasFDerivAt g D (p, 0) := (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hinc : HasFDerivAt (fun S : E => (p, S)) (ContinuousLinearMap.inr ℝ P E) 0 :=
    (hasFDerivAt_const p 0).prodMk (hasFDerivAt_id 0)
  have hpart : D.comp (ContinuousLinearMap.inr ℝ P E) = (L : E →L[ℝ] V) :=
    (hd.comp 0 hinc).unique hL
  let K := parameterBlockEquiv (D.comp (ContinuousLinearMap.inl ℝ P E)) L
  have hK : (K : P × E →L[ℝ] P × V) = (ContinuousLinearMap.fst ℝ P E).prod D :=
    parameterBlockEquiv_of_partial D L (fun v => congrArg (fun T : E →L[ℝ] V => T v) hpart)
  let G : P × E → P × V := fun x => (x.1, g x)
  have hG : ContDiffAt ℝ ⊤ G (p, 0) := (contDiff_fst.prodMk hg).contDiffAt
  have hG' : HasFDerivAt G (K : P × E →L[ℝ] P × V) (p, 0) := by
    rw [hK]
    exact hasFDerivAt_fst.prodMk hd
  let inv := hG.localInverse hG' (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
  have hv : G (p, 0) = (p, 0) := by simp [G, hzero]
  have hinv : inv (p, 0) = (p, 0) := by
    rw [← hv]
    exact hG.localInverse_apply_image hG' (by simp)
  have hsmooth : ContDiffAt ℝ ⊤ inv (p, 0) := by
    rw [← hv]
    exact hG.to_localInverse hG' (by simp)
  have he : ∀ᶠ y in 𝓝 (p, (0 : V)), G (inv y) = y := by
    rw [← hv]
    exact (hG.hasStrictFDerivAt' hG' (by simp)).eventually_right_inverse
  refine ⟨fun q => (inv (q, 0)).2, ?_, ?_, ?_⟩
  · simp [hinv]
  · exact (hsmooth.comp p (contDiffAt_id.prodMk contDiffAt_const)).snd
  · have ht : Filter.Tendsto (fun q : P => (q, (0 : V))) (𝓝 p) (𝓝 (p, 0)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually he] with q hq
    have hfst : (inv (q, 0)).1 = q := congrArg Prod.fst hq
    have hsnd : g (inv (q, 0)) = 0 := congrArg Prod.snd hq
    calc
      g (q, (inv (q, 0)).2) = g (inv (q, 0)) := congrArg g (Prod.ext hfst.symm rfl)
      _ = 0 := hsnd

end PaperI
