import PaperILean.ParameterImplicitFunction

/-! The original parameter implicit function theorem, with local finite
smoothness, an arbitrary base root, and local uniqueness of every nearby zero.
This is qualitative: no uniform radius or parameter-compatible chart choice.
-/
noncomputable section
namespace PaperI
open Filter
open scoped Topology

theorem original_parameter_local_zero
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : P × E → V) (p : P) (x : E) (n : WithTop ℕ∞) (hn : 1 ≤ n)
    (hg : ContDiffAt ℝ n g (p,x)) (hzero : g (p,x)=0)
    (L : E ≃L[ℝ] V)
    (hL : HasFDerivAt (fun t : E => g (p,t)) (L : E →L[ℝ] V) x) :
    ∃ c : P → E, c p=x ∧ ContDiffAt ℝ n c p ∧
      (∀ᶠ q in 𝓝 p, g (q,c q)=0) ∧
      (∀ᶠ u in 𝓝 (p,x), g u=0 → u.2=c u.1) := by
  let D := fderiv ℝ g (p,x)
  have hd : HasFDerivAt g D (p,x) := (hg.differentiableAt hn).hasFDerivAt
  have hinc : HasFDerivAt (fun t : E => (p,t)) (ContinuousLinearMap.inr ℝ P E) x :=
    (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  have hpart : D.comp (ContinuousLinearMap.inr ℝ P E)=(L : E →L[ℝ] V) :=
    (hd.comp x hinc).unique hL
  let K := parameterBlockEquiv (D.comp (ContinuousLinearMap.inl ℝ P E)) L
  have hK : (K : P × E →L[ℝ] P × V)=(ContinuousLinearMap.fst ℝ P E).prod D :=
    parameterBlockEquiv_of_partial D L (fun v => congrArg (fun T : E →L[ℝ] V => T v) hpart)
  let H : P × E → P × V := fun u => (u.1,g u)
  have hH : ContDiffAt ℝ n H (p,x) := contDiffAt_fst.prodMk hg
  have hH' : HasFDerivAt H (K : P × E →L[ℝ] P × V) (p,x) := by
    rw [hK]
    exact hasFDerivAt_fst.prodMk hd
  let inv := hH.localInverse hH' hn
  have hv : H (p,x)=(p,0) := by simp [H,hzero]
  have hinv : inv (p,0)=(p,x) := by
    rw [← hv]
    exact hH.localInverse_apply_image hH' hn
  have hsmooth : ContDiffAt ℝ n inv (p,0) := by
    rw [← hv]
    exact hH.to_localInverse hH' hn
  have hright : ∀ᶠ u in 𝓝 (p,(0 : V)), H (inv u)=u := by
    rw [← hv]
    exact (hH.hasStrictFDerivAt' hH' hn).eventually_right_inverse
  have hleft : ∀ᶠ u in 𝓝 (p,x), inv (H u)=u :=
    (hH.hasStrictFDerivAt' hH' hn).eventually_left_inverse
  refine ⟨fun q => (inv (q,0)).2,?_,?_,?_,?_⟩
  · simp [hinv]
  · exact (hsmooth.comp p (contDiffAt_id.prodMk contDiffAt_const)).snd
  · have ht : Tendsto (fun q : P => (q,(0 : V))) (𝓝 p) (𝓝 (p,0)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually hright] with q hq
    have hf : (inv (q,0)).1=q := congrArg Prod.fst hq
    have hz : g (inv (q,0))=0 := congrArg Prod.snd hq
    calc
      g (q,(inv (q,0)).2)=g (inv (q,0)) := congrArg g (Prod.ext hf.symm rfl)
      _=0 := hz
  · filter_upwards [hleft] with u hu hzu
    have he : H u=(u.1,0) := by simp [H,hzu]
    rw [he] at hu
    exact (congrArg Prod.snd hu).symm

end PaperI
