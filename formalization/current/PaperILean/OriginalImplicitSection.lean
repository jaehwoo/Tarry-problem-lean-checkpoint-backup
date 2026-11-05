import PaperILean.OriginalNormalImplicitFunction

/-! The manuscript's local uniqueness argument on a selected continuous
section. Relative neighborhoods are essential at cell boundaries. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology

theorem original_parameter_section_agreesWithin
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    (g : P × E → V) (p : P) (x : E) (S : Set P) (b c : P → E)
    (hunique : ∀ᶠ u in 𝓝 (p,x), g u=0 → u.2=c u.1)
    (hb : ContinuousWithinAt b S p) (hbv : b p=x)
    (hroot : ∀ᶠ q in 𝓝[S] p, g (q,b q)=0) :
    b =ᶠ[𝓝[S] p] c := by
  have ht : Tendsto (fun q => (q,b q)) (𝓝[S] p) (𝓝 (p,x)) := by
    have h : Tendsto (fun q => (q,b q)) (𝓝[S] p) (𝓝 (p,b p)) :=
      continuousWithinAt_id.prodMk hb
    rwa [hbv] at h
  filter_upwards [ht.eventually hunique,hroot] with q hq hz
  exact hq hz

theorem original_parameter_selected_extension
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : P × E → V) (p : P) (S : Set P) (b : P → E)
    (n : WithTop ℕ∞) (hn : 1≤n)
    (hg : ContDiffAt ℝ n g (p,b p)) (hzero : g (p,b p)=0)
    (L : E ≃L[ℝ] V)
    (hL : HasFDerivAt (fun t => g (p,t)) (L : E →L[ℝ] V) (b p))
    (hb : ContinuousWithinAt b S p)
    (hroot : ∀ᶠ q in 𝓝[S] p, g (q,b q)=0) :
    ∃ c : P → E, c p=b p ∧ ContDiffAt ℝ n c p ∧
      (∀ᶠ q in 𝓝 p, g (q,c q)=0) ∧
      (∀ᶠ u in 𝓝 (p,b p), g u=0 → u.2=c u.1) ∧
      b =ᶠ[𝓝[S] p] c := by
  obtain ⟨c,hc,hs,hz,hu⟩ := original_parameter_local_zero g p (b p) n hn hg hzero L hL
  exact ⟨c,hc,hs,hz,hu,original_parameter_section_agreesWithin g p (b p) S b c hu hb rfl hroot⟩

theorem original_parameter_selected_contDiffWithinAt
    {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : P × E → V) (p : P) (S : Set P) (b : P → E)
    (n : WithTop ℕ∞) (hn : 1≤n)
    (hg : ContDiffAt ℝ n g (p,b p)) (hzero : g (p,b p)=0)
    (L : E ≃L[ℝ] V)
    (hL : HasFDerivAt (fun t => g (p,t)) (L : E →L[ℝ] V) (b p))
    (hb : ContinuousWithinAt b S p)
    (hroot : ∀ᶠ q in 𝓝[S] p, g (q,b q)=0) :
    ContDiffWithinAt ℝ n b S p := by
  obtain ⟨c,hc,hs,_,_,heq⟩ := original_parameter_selected_extension g p S b n hn hg hzero L hL hb hroot
  exact hs.contDiffWithinAt.congr_of_eventuallyEq heq hc.symm

end PaperI
