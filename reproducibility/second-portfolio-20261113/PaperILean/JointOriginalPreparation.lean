import PaperILean.JointGoodIntervalSelection
import PaperILean.PolynomialSignPullback

/-! Assemble the ORIGINAL regular-cut / divided-difference / simultaneous
good-set / CAD-selection route on the SAME jointly represented centerline.
The auxiliary scalar is centered only for amplitude; geometry is unchanged.
This fixed-joint-family theorem is not an input-format-only strip theorem. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointCenteredScalarGraph {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set (((α ⊕ Unit) ⊕ Fin 2) → ℝ) :=
  {v | Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
    ![v (Sum.inr 0),v (Sum.inr 1)+v (Sum.inl (Sum.inr ()))]∈G}

theorem jointCenteredScalarGraph_definable
    (hQE : PublishedRealSemialgebraicity) {α : Type} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (jointCenteredScalarGraph G) := by
  let q : α ⊕ Fin 2 → MvPolynomial ((α ⊕ Unit) ⊕ Fin 2) ℝ :=
    Sum.elim (fun c => MvPolynomial.X (Sum.inl (Sum.inl c)))
      ![MvPolynomial.X (Sum.inr 0),MvPolynomial.X (Sum.inr 1)+MvPolynomial.X (Sum.inl (Sum.inr ()))]
  have h := hasPolynomialSignDescription_definable
    (hasPolynomialSignDescription_polynomial_preimage (hQE.finite_sign_description _ hG) q)
  convert h using 1
  ext v
  have he : (fun i => MvPolynomial.eval v (q i)) =
      Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr 0),v (Sum.inr 1)+v (Sum.inl (Sum.inr ()))] := by
    funext i
    rcases i with i | i
    · simp [q]
    · fin_cases i <;> simp [q]
  simp only [jointCenteredScalarGraph,mem_setOf_eq,he]

theorem jointCenteredScalarGraph_realize {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ))
    (p : α → ℝ) (f : ℝ → ℝ) (J : Set ℝ)
    (hrep : ∀ x∈J, ∀ y, Sum.elim p ![x,y]∈G ↔ y=f x)
    (c x y : ℝ) (hx : x∈J) :
    Sum.elim (Sum.elim p (fun _ => c)) ![x,y]∈jointCenteredScalarGraph G ↔ y=f x-c := by
  change Sum.elim p ![x,y+c]∈G ↔ _
  rw [hrep x hx]
  exact eq_sub_iff_add_eq.symm

/-- Joint graph correctness, not a separate measurability hypothesis on the
values, supplies evaluation at a Borel input. No values outside this graph
fiber are used to identify the actual function. -/
theorem published_measurable_scalar_graph_value
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G)
    {Ω : Type*} [MeasurableSpace Ω] (p : Ω → α → ℝ) (x y : Ω → ℝ)
    (hp : Measurable p) (hx : Measurable x)
    (hrep : ∀ ω z, Sum.elim (p ω) ![x ω,z]∈G ↔ z=y ω) : Measurable y := by
  obtain ⟨F,hFm,_,hFR⟩ := published_joint_scalar_selector hCAD hQE hHardt
    (scalarGraphAsUnit G) (scalarGraphAsUnit_definable hG)
  let q : Ω → (α ⊕ Unit) → ℝ := fun ω => Sum.elim (p ω) (fun _ => x ω)
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro i
    rcases i with i | ⟨⟩
    · exact (measurable_pi_apply i).comp hp
    · exact hx
  have he : y=F ∘ q := by
    funext ω
    have hD : q ω∈projectionDomain (scalarGraphAsUnit G) :=
      ⟨fun _ => y ω,(hrep ω (y ω)).mpr rfl⟩
    exact ((hrep ω (F (q ω))).mp (hFR _ hD)).symm
  rw [he]
  exact hFm.comp hq

/-- Fixed joint graph, then constants and selectors, then arbitrary Borel
parameters/endpoints. All orders including zero are for the centered scalar;
positive orders are also for the unchanged geometric function. -/
theorem published_joint_original_lipschitz_prepared_interval
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (p : Ω → α → ℝ) (f : Ω → ℝ → ℝ)
      (a b : Ω → ℝ), Measurable p → Measurable a → Measurable b → (∀ ω, a ω<b ω) →
      (∀ ω, ∀ x∈Icc (a ω) (b ω), ∀ y, Sum.elim (p ω) ![x,y]∈G ↔ y=f ω x) →
      (∀ ω, LipschitzOnWith 1 (f ω) (Icc (a ω) (b ω))) →
      ∃ u v : Ω → ℝ, Measurable u ∧ Measurable v ∧ ∀ ω,
        u ω<v ω ∧ Icc (u ω) (v ω)⊆Icc (a ω) (b ω) ∧
        (b ω-a ω)/(K : ℝ)≤v ω-u ω ∧ AnalyticOnNhd ℝ (f ω) (Icc (u ω) (v ω)) ∧
        (∀ x∈Icc (u ω) (v ω), ∀ n≤N,
          |iteratedDeriv n (fun q => f ω q-f ω (a ω)) x|≤C*(b ω-a ω)/(b ω-a ω)^n) ∧
        (∀ x∈Icc (u ω) (v ω), ∀ n, 0<n → n≤N →
          |iteratedDeriv n (f ω) x|≤C*(b ω-a ω)/(b ω-a ω)^n) := by
  obtain ⟨KA,E,hKA,hEm,_,hregular⟩ := published_joint_original_regular_interval
    hCAD hCell hHardt hQE hPiece G hG
  obtain ⟨C,hC,KG,hKG,hprep⟩ := published_joint_original_prepared_interval
    hDD hCAD hCell hHardt hQE (jointCenteredScalarGraph G) (jointCenteredScalarGraph_definable hQE hG) N
  have hKA1 : 1≤(KA : ℝ) := by exact_mod_cast hKA
  have hCfull : 1≤C*(KA : ℝ)^N := calc
    1 ≤ C := hC
    _ = C*1 := by ring
    _ ≤ C*(KA : ℝ)^N := mul_le_mul_of_nonneg_left (one_le_pow₀ hKA1) (zero_le_one.trans hC)
  refine ⟨C*(KA : ℝ)^N,hCfull,KA*KG,Nat.mul_pos hKA hKG,?_⟩
  intro Ω inst p f a b hp ha hb hab hrep hLip
  let q : Ω → (α ⊕ Fin 2) → ℝ := fun ω => Sum.elim (p ω) ![a ω,b ω]
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro i
    rcases i with i | i
    · exact (measurable_pi_apply i).comp hp
    · fin_cases i <;> assumption
  let l : Ω → ℝ := fun ω => E (q ω) 0
  let r : Ω → ℝ := fun ω => E (q ω) 1
  have hl : Measurable l := (measurable_pi_apply 0).comp (hEm.comp hq)
  have hr : Measurable r := (measurable_pi_apply 1).comp (hEm.comp hq)
  have hreg (ω) := hregular (p ω) (f ω) (a ω) (b ω) (hab ω) (hrep ω)
  have hinside (ω) : Ioo (l ω) (r ω)⊆Icc (a ω) (b ω) :=
    fun x hx => ⟨(hreg ω).1.trans hx.1.le,hx.2.le.trans (hreg ω).2.2.1⟩
  have hval : Measurable (fun ω => f ω (a ω)) := published_measurable_scalar_graph_value
    hCAD hQE hHardt G hG p a (fun ω => f ω (a ω)) hp ha
      (fun ω => hrep ω (a ω) ⟨le_rfl,(hab ω).le⟩)
  let pc : Ω → (α ⊕ Unit) → ℝ := fun ω => Sum.elim (p ω) (fun _ => f ω (a ω))
  have hpc : Measurable pc := by
    apply measurable_pi_lambda
    intro i
    rcases i with i | ⟨⟩
    · exact (measurable_pi_apply i).comp hp
    · exact hval
  obtain ⟨u,v,hum,hvm,hgood⟩ := hprep Ω pc (fun ω q => f ω q-f ω (a ω))
    (fun ω => b ω-a ω) l r hpc (hb.sub ha) hl hr
    (fun ω => sub_pos.mpr (hab ω)) (fun ω => (hreg ω).2.1)
    (fun ω x hx y => jointCenteredScalarGraph_realize G (p ω) (f ω) (Icc (a ω) (b ω))
      (hrep ω) (f ω (a ω)) x y (hinside ω hx))
    (fun ω => centered_contDiffOn (hreg ω).2.2.2.2.1.contDiffOn_of_completeSpace (a ω))
    (fun ω x hx => centered_one_lipschitz_amplitude (hLip ω) ⟨le_rfl,(hab ω).le⟩ (hinside ω hx))
  refine ⟨u,v,hum,hvm,?_⟩
  intro ω
  obtain ⟨huv,hsub,hlen,hbound⟩ := hgood ω
  have hfull : (b ω-a ω)/((KA*KG : ℕ) : ℝ)≤v ω-u ω := calc
    _ = ((b ω-a ω)/(KA : ℝ))/(KG : ℝ) := by rw [Nat.cast_mul,div_div]
    _ ≤ (r ω-l ω)/(KG : ℝ) := div_le_div_of_nonneg_right (hreg ω).2.2.2.1 (Nat.cast_nonneg KG)
    _ ≤ v ω-u ω := hlen
  have hbnd : ∀ x∈Icc (u ω) (v ω), ∀ n≤N,
      |iteratedDeriv n (fun q => f ω q-f ω (a ω)) x|≤(C*(KA : ℝ)^N)*(b ω-a ω)/(b ω-a ω)^n := by
    intro x hx n hn
    exact (hbound x hx n hn).trans (preparation_derivative_scale_comparison
      (zero_le_one.trans hC) (sub_nonneg.mpr (hab ω).le) (sub_pos.mpr (hab ω)) hKA (hreg ω).2.2.2.1 hn)
  refine ⟨huv,hsub.trans (hinside ω),hfull,(hreg ω).2.2.2.2.1.mono hsub,hbnd,?_⟩
  intro x hx n hn hN
  rw [← iteratedDeriv_centered (f ω) (a ω) x n hn]
  exact hbnd x hx n hN

end PaperI
