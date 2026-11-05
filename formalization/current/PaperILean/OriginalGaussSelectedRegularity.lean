import PaperILean.OriginalGaussParameterIFT

/-! Original IFT route for a continuous selected regular root on any domain.
No interior, boundedness, sign, or global branch-uniqueness premise is added.
Smoothness is relative to the domain, with local ambient extensions. -/
noncomputable section
namespace PaperI
open Set Filter
open scoped Topology ContDiff

theorem originalGauss_selected_local_extension {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (S : Set (Fin 2 → ℝ)) (b : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (a : Fin 2 → ℝ)
    (ha : a∈S) (hb : ContinuousWithinAt b S a)
    (hroot : ∀ q∈S, b q∈originalGaussRegularRootSet F n (q 0) (q 1)) :
    ∃ c : (Fin 2 → ℝ) → (Fin 2 → ℝ), c a=b a ∧ ContDiffAt ℝ ∞ c a ∧
      (∀ᶠ q in 𝓝 a, originalGaussParameterEquations F n (q,c q)=0) ∧
      (∀ᶠ u in 𝓝 (a,b a), originalGaussParameterEquations F n u=0 → u.2=c u.1) ∧
      b =ᶠ[𝓝[S] a] c := by
  obtain ⟨c,hc,hs,hz,hu⟩ := originalGauss_regular_parameter_local_branch F n a (b a) (hroot a ha)
  refine ⟨c,hc,hs,hz,hu,original_parameter_section_agreesWithin _ a (b a) S b c hu hb rfl ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact originalGaussParameterEquations_zero F n q (b q) (hroot q hq)

theorem originalGauss_selected_contDiffOn {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (S : Set (Fin 2 → ℝ)) (b : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hb : ContinuousOn b S)
    (hroot : ∀ q∈S, b q∈originalGaussRegularRootSet F n (q 0) (q 1)) :
    ContDiffOn ℝ ∞ b S := by
  intro a ha
  obtain ⟨c,hc,hs,_,_,heq⟩ := originalGauss_selected_local_extension F n S b a ha (hb a ha) hroot
  exact hs.contDiffWithinAt.congr_of_eventuallyEq heq hc.symm

/-- A single ambient extension is C1 on an actual open neighborhood and
agrees with the original section on that neighborhood intersected with S.
The neighborhood may depend on F, the branch and the base point. -/
theorem originalGauss_selected_open_extension {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (S : Set (Fin 2 → ℝ)) (b : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (a : Fin 2 → ℝ)
    (ha : a∈S) (hb : ContinuousWithinAt b S a)
    (hroot : ∀ q∈S, b q∈originalGaussRegularRootSet F n (q 0) (q 1)) :
    ∃ c : (Fin 2 → ℝ) → (Fin 2 → ℝ), ∃ U : Set (Fin 2 → ℝ),
      IsOpen U ∧ a∈U ∧ c a=b a ∧ ContDiffOn ℝ 1 c U ∧
      (∀ q∈U, originalGaussParameterEquations F n (q,c q)=0) ∧
      EqOn b c (U∩S) ∧
      (∀ᶠ u in 𝓝 (a,b a), originalGaussParameterEquations F n u=0 → u.2=c u.1) := by
  obtain ⟨c,hc,hs,hz,hu,heq⟩ := originalGauss_selected_local_extension F n S b a ha hb hroot
  have hs1 : ContDiffAt ℝ 1 c a := hs.of_le (by simp)
  have hall : ∀ᶠ q in 𝓝 a, ContDiffAt ℝ 1 c q ∧
      originalGaussParameterEquations F n (q,c q)=0 ∧ (q∈S → b q=c q) :=
    (hs1.eventually (by simp)).and (hz.and (eventually_nhdsWithin_iff.mp heq))
  obtain ⟨U,hU,hopen,haU⟩ := mem_nhds_iff.mp hall
  exact ⟨c,U,hopen,haU,hc,fun q hq => (hU hq).1.contDiffWithinAt,
    fun q hq => (hU hq).2.1,fun q hq => (hU hq.1).2.2 hq.2,hu⟩

theorem originalGauss_selected_overlap_unique {k : ℕ} (F : CoefficientSpace k) (n : ℕ)
    (S T : Set (Fin 2 → ℝ)) (b c : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (a : Fin 2 → ℝ)
    (ha : a∈S) (hb : ContinuousWithinAt b S a) (hc : ContinuousWithinAt c T a)
    (hba : b a=c a)
    (hrootb : ∀ q∈S, b q∈originalGaussRegularRootSet F n (q 0) (q 1))
    (hrootc : ∀ q∈T, c q∈originalGaussRegularRootSet F n (q 0) (q 1)) :
    b =ᶠ[𝓝[S∩T] a] c := by
  obtain ⟨e,_,_,_,hu,hbe⟩ := originalGauss_selected_local_extension F n S b a ha hb hrootb
  have hce : c =ᶠ[𝓝[T] a] e := by
    apply original_parameter_section_agreesWithin _ a (b a) T c e hu hc hba.symm
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact originalGaussParameterEquations_zero F n q (c q) (hrootc q hq)
  exact (hbe.filter_mono (nhdsWithin_mono _ inter_subset_left)).trans
    (hce.filter_mono (nhdsWithin_mono _ inter_subset_right)).symm

end PaperI
