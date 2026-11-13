import PaperILean.JointRegularIntervalSelection
import PaperILean.PreparedCenterlineInterval

/-! Original simultaneous strict derivative tests, their actual comparable
mass, and one joint retained closed interval. The good set is not assumed
connected; its COMPLETE-family component bound is used. -/
noncomputable section
namespace PaperI
open Set FirstOrder MeasureTheory
open scoped ENNReal
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def retainedIntervalRelation {α : Type*} (R : Set ((α ⊕ Unit) → ℝ)) :
    Set (((α ⊕ Unit) ⊕ Fin 2) → ℝ) :=
  {v | v (Sum.inr 0)<v (Sum.inr 1) ∧
    v (Sum.inl (Sum.inr ()))≤v (Sum.inr 1)-v (Sum.inr 0) ∧
    ∀ x∈Icc (v (Sum.inr 0)) (v (Sum.inr 1)),
      Sum.elim (fun c => v (Sum.inl (Sum.inl c))) (fun _ => x)∈R}

theorem retainedIntervalRelation_definable {α : Type} [Finite α]
    {R : Set ((α ⊕ Unit) → ℝ)} (hR : (univ : Set ℝ).Definable Language.ring R) :
    (univ : Set ℝ).Definable Language.ring (retainedIntervalRelation R) := by
  let B := (α ⊕ Unit) ⊕ Fin 2
  let e : α ⊕ Unit → B ⊕ Unit :=
    Sum.elim (fun c => Sum.inl (Sum.inl (Sum.inl c))) Sum.inr
  have hl := realPolynomial_le_definable (MvPolynomial.X (Sum.inl (Sum.inr 0) : B ⊕ Unit))
    (MvPolynomial.X (Sum.inr ()))
  have hr := realPolynomial_le_definable (MvPolynomial.X (Sum.inr () : B ⊕ Unit))
    (MvPolynomial.X (Sum.inl (Sum.inr 1)))
  have hAll := realDefinable_forall ((hl.inter hr).compl.union (hR.preimage_comp e))
  have hsub : (univ : Set ℝ).Definable Language.ring
      {v : B → ℝ | ∀ x∈Icc (v (Sum.inr 0)) (v (Sum.inr 1)),
        Sum.elim (fun c => v (Sum.inl (Sum.inl c))) (fun _ => x)∈R} := by
    convert hAll using 1
    ext v
    have he (x : Unit → ℝ) : Sum.elim v x ∘ e =
        Sum.elim (fun c => v (Sum.inl (Sum.inl c))) (fun _ => x ()) := by
      funext z; cases z <;> rfl
    simp only [mem_setOf_eq,mem_union,mem_compl_iff,mem_inter_iff,mem_preimage,he,
      MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr]
    constructor
    · intro h x
      by_cases hx : x ()∈Icc (v (Sum.inr 0)) (v (Sum.inr 1))
      · exact Or.inr (h (x ()) hx)
      · exact Or.inl hx
    · intro h x hx
      exact (h (fun _ => x)).resolve_left (not_not.mpr hx)
  have hlt := realCoordinate_lt_definable (Sum.inr (0 : Fin 2) : B) (Sum.inr 1)
  have hm := realPolynomial_le_definable (MvPolynomial.X (Sum.inl (Sum.inr ()) : B))
    (MvPolynomial.X (Sum.inr 1)-MvPolynomial.X (Sum.inr 0))
  have hm' : (univ : Set ℝ).Definable Language.ring
      {v : B → ℝ | v (Sum.inl (Sum.inr ()))≤v (Sum.inr 1)-v (Sum.inr 0)} := by
    simpa only [map_sub,MvPolynomial.eval_X] using hm
  exact hlt.inter (hm'.inter hsub)

theorem published_joint_retained_interval_selector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] (R : Set ((α ⊕ Unit) → ℝ))
    (hR : (univ : Set ℝ).Definable Language.ring R) :
    ∃ E : ((α ⊕ Unit) → ℝ) → Fin 2 → ℝ, Measurable E ∧
      HasPolynomialSignDescription (selectedFunctionGraph univ E) ∧
      ∀ (p : α → ℝ) (a b M : ℝ) (K : ℕ),
      IsOpen (scalarProjectionFiber R p) → scalarProjectionFiber R p ⊆ Ioo a b → 0<M →
      Finite (ConnectedComponents (scalarProjectionFiber R p)) →
      Nat.card (ConnectedComponents (scalarProjectionFiber R p))≤K →
      M≤volume.real (scalarProjectionFiber R p) →
      let e := E (Sum.elim p (fun _ => M/(2*((K : ℝ)+1))))
      e 0<e 1 ∧ M/(2*((K : ℝ)+1))≤e 1-e 0 ∧ Icc (e 0) (e 1)⊆scalarProjectionFiber R p := by
  obtain ⟨E,hEm,hEs,hER⟩ := published_joint_vector_selector hCAD hQE hHardt
    (retainedIntervalRelation R) (retainedIntervalRelation_definable hR)
  refine ⟨E,hEm,hEs,?_⟩
  intro p a b M K ho hsub hM hfin hK hmass
  letI := hfin
  obtain ⟨u,v,huv,hinside,hlen⟩ := exists_closed_interval_of_open_component_mass ho hsub hM hK hmass
  have hp : Sum.elim p (fun _ => M/(2*((K : ℝ)+1)))∈projectionDomain (retainedIntervalRelation R) :=
    ⟨![u,v],huv,hlen,hinside⟩
  exact hER _ hp

/-- The strict good set contains the original divided-difference good set.
The factor two is a strict margin, not a change of the geometric function. -/
theorem published_uniform_strict_preparation_mass
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (B a b : ℝ),
      0<B → a<b → (∀ x∈Ioo a b, ∀ y, Sum.elim p ![x,y]∈G ↔ y=f x) →
      ContDiffOn ℝ N f (Ioo a b) → (∀ x∈Ioo a b, |f x|≤B) →
      let U := strictDerivativeGoodSet f N a b (fun n => C*B/(b-a)^n.val)
      IsOpen U ∧ U⊆Ioo a b ∧ (b-a)/2≤volume.real U ∧
        Finite (ConnectedComponents U) ∧ Nat.card (ConnectedComponents U)≤K := by
  obtain ⟨KS,hKS⟩ := published_uniform_iteratedDerivative_superlevel_components hCell hHardt hQE G hG N
  obtain ⟨C,hC,hprep⟩ := published_finite_list_preparation_of_component_bound
    (ι := Unit) hDD N KS (1/2) (by norm_num)
  obtain ⟨K,hK⟩ := published_uniform_strictDerivativeGoodSet_components hCell hHardt hQE G hG N
  refine ⟨2*C,by linarith,K,?_⟩
  intro p f B a b hB hab hrep hf hamp
  obtain ⟨V,hVm,hVsub,hbad,hgood⟩ := hprep (fun _ => f) (fun _ => B) a b hab
    (fun _ => hB.le) (fun _ => hf) (fun _ => hamp)
    (fun _ n hn threshold sign _ => hKS p f a b threshold sign hrep hf n hn)
  let T : Fin (N+1) → ℝ := fun n => 2*C*B/(b-a)^n.val
  let U := strictDerivativeGoodSet f N a b T
  have hUsub : U⊆Ioo a b := fun _ hx => hx.1
  have hVU : V⊆U := by
    intro x hx
    refine ⟨hVsub hx,?_⟩
    intro n
    have hp : 0<C*B/(b-a)^n.val := div_pos
      (mul_pos (lt_of_lt_of_le zero_lt_one hC) hB) (pow_pos (sub_pos.mpr hab) _)
    have hg := hgood x hx () n.val (Nat.lt_succ_iff.mp n.isLt)
    change |iteratedDeriv n.val f x|<2*C*B/(b-a)^n.val
    calc
      _ ≤ C*B/(b-a)^n.val := hg
      _ < 2*(C*B/(b-a)^n.val) := by linarith
      _ = 2*C*B/(b-a)^n.val := by ring
  have hfinite : volume U≠⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono hUsub)
  have hmass : (b-a)/2≤volume.real U :=
    (preparation_half_good_mass hab hVm hVsub (by convert hbad using 2 <;> ring)).trans
      (measureReal_mono hVU hfinite)
  exact ⟨isOpen_strictDerivativeGoodSet hf T,hUsub,hmass,hK p f a b T hrep hf⟩

/-- Original one-variable preparation with Borel retained endpoints. Constants
depend on the FIXED JOINT graph and N, not its parameters or substitutions.
An input-format-only application is a separate quantified specialization. -/
theorem published_joint_original_prepared_interval
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (p : Ω → α → ℝ) (f : Ω → ℝ → ℝ)
      (B a b : Ω → ℝ), Measurable p → Measurable B → Measurable a → Measurable b →
      (∀ ω, 0<B ω) → (∀ ω, a ω<b ω) →
      (∀ ω, ∀ x∈Ioo (a ω) (b ω), ∀ y, Sum.elim (p ω) ![x,y]∈G ↔ y=f ω x) →
      (∀ ω, ContDiffOn ℝ N (f ω) (Ioo (a ω) (b ω))) →
      (∀ ω, ∀ x∈Ioo (a ω) (b ω), |f ω x|≤B ω) →
      ∃ u v : Ω → ℝ, Measurable u ∧ Measurable v ∧ ∀ ω,
        u ω<v ω ∧ Icc (u ω) (v ω)⊆Ioo (a ω) (b ω) ∧
        (b ω-a ω)/(K : ℝ)≤v ω-u ω ∧
        ∀ x∈Icc (u ω) (v ω), ∀ n≤N, |iteratedDeriv n (f ω) x|≤C*B ω/(b ω-a ω)^n := by
  obtain ⟨C,hC,K,hprep⟩ := published_uniform_strict_preparation_mass hDD hCell hHardt hQE G hG N
  obtain ⟨E,hEm,hEs,hER⟩ := published_joint_retained_interval_selector hCAD hQE hHardt
    (derivativeGoodRelation G N) (derivativeGoodRelation_definable hG N)
  refine ⟨C,hC,4*(K+1),by omega,?_⟩
  intro Ω inst p f B a b hp hB ha hb hBpos hab hrep hf hamp
  let T : Ω → Fin (N+1) → ℝ := fun ω n => C*B ω/(b ω-a ω)^n.val
  let q : Ω → (α ⊕ (Fin 2 ⊕ Fin (N+1))) → ℝ :=
    fun ω => Sum.elim (p ω) (Sum.elim ![a ω,b ω] (T ω))
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro j
    rcases j with j | (j | n)
    · exact (measurable_pi_apply j).comp hp
    · fin_cases j <;> assumption
    · exact (measurable_const.mul hB).div ((hb.sub ha).pow_const n.val)
  let z : Ω → ((α ⊕ (Fin 2 ⊕ Fin (N+1))) ⊕ Unit) → ℝ :=
    fun ω => Sum.elim (q ω) (fun _ => ((b ω-a ω)/2)/(2*((K : ℝ)+1)))
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro j
    rcases j with j | ⟨⟩
    · exact (measurable_pi_apply j).comp hq
    · exact ((hb.sub ha).div_const 2).div_const _
  refine ⟨fun ω => E (z ω) 0,fun ω => E (z ω) 1,
    (measurable_pi_apply 0).comp (hEm.comp hz),(measurable_pi_apply 1).comp (hEm.comp hz),?_⟩
  intro ω
  have he : scalarProjectionFiber (derivativeGoodRelation G N) (q ω) =
      strictDerivativeGoodSet (f ω) N (a ω) (b ω) (T ω) := by
    ext x
    exact derivativeGoodRelation_realize_iff G (p ω) (f ω) (a ω) (b ω) N (T ω) (hrep ω) (hf ω) x
  obtain ⟨ho,hsub,hmass,hfin,hcount⟩ := hprep (p ω) (f ω) (B ω) (a ω) (b ω)
    (hBpos ω) (hab ω) (hrep ω) (hf ω) (hamp ω)
  obtain ⟨huv,hlen,hinside⟩ := hER (q ω) (a ω) (b ω) ((b ω-a ω)/2) K
    (he.symm ▸ ho) (he.symm ▸ hsub) (div_pos (sub_pos.mpr (hab ω)) (by norm_num))
    (he.symm ▸ hfin) (he.symm ▸ hcount) (he.symm ▸ hmass)
  have hi : Icc (E (z ω) 0) (E (z ω) 1)⊆strictDerivativeGoodSet (f ω) N (a ω) (b ω) (T ω) :=
    fun x hx => he ▸ hinside hx
  refine ⟨huv,hi.trans hsub,?_,?_⟩
  · have hc : ((4*(K+1) : ℕ) : ℝ)=2*(2*((K : ℝ)+1)) := by push_cast; ring
    rw [hc]
    simpa only [z,div_div] using hlen
  · intro x hx n hn
    exact ((hi hx).2 ⟨n,Nat.lt_succ_iff.mpr hn⟩).le

end PaperI
