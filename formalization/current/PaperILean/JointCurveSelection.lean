import PaperILean.JointCurveSelectionRegularity

/-! Parameter-compatible curve selection for a fixed joint family and a
semialgebraic section of its fiberwise closures. Continuity is in time for
each parameter; no joint continuity in the parameter is asserted. -/

noncomputable section
namespace PaperI
open Set FirstOrder Filter
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def attachAtZero {ρ κ : Type*} (a : (ρ → ℝ) → κ → ℝ)
    (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ) (p : ρ → ℝ) (t : ℝ) : κ → ℝ :=
  if t = 0 then a p else f (Sum.elim p (fun _ => t))

theorem attachAtZero_zero {ρ κ : Type*} (a : (ρ → ℝ) → κ → ℝ)
    (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ) (p : ρ → ℝ) :
    attachAtZero a f p 0 = a p := by simp [attachAtZero]

theorem attachAtZero_positive {ρ κ : Type*} (a : (ρ → ℝ) → κ → ℝ)
    (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ) (p : ρ → ℝ) {t : ℝ} (ht : 0 < t) :
    attachAtZero a f p t = f (Sum.elim p (fun _ => t)) := by
  simp only [attachAtZero, ne_of_gt ht, if_false]

theorem attachAtZero_continuousOn {ρ κ : Type} [Fintype κ]
    (a : (ρ → ℝ) → κ → ℝ) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (p : ρ → ℝ) (ε : ℝ)
    (hnear : ∀ t : ℝ, 0 < t → ∀ k, |f (Sum.elim p (fun _ => t)) k - a p k| < t)
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ k,
      DifferentiableAt ℝ (fun u => f (Sum.elim p (fun _ => u)) k) t) :
    ContinuousOn (attachAtZero a f p) (Ico (0 : ℝ) ε) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    apply Metric.continuousWithinAt_iff.mpr
    intro η hη
    refine ⟨η,hη,fun u hu huη => ?_⟩
    by_cases hu0 : u = 0
    · simpa only [hu0, dist_self] using hη
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [attachAtZero_zero, attachAtZero_positive a f p huPos]
    apply (dist_pi_lt_iff hη).mpr
    intro k
    rw [Real.dist_eq]
    exact (hnear u huPos k).trans (by simpa only [Real.dist_eq, sub_zero, abs_of_pos huPos] using huη)
  · have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hc : ContinuousAt (fun u => f (Sum.elim p (fun _ => u))) t :=
      continuousAt_pi.mpr (fun k => (hdiff t ⟨htPos,ht.2⟩ k).continuousAt)
    apply ContinuousAt.continuousWithinAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds htPos] with u hu
    exact attachAtZero_positive a f p hu

def jointCurveGermGraph {ρ κ : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  {v | v ∘ Sum.inl ∈ P ∧
    v ∘ Sum.inr ∈ curveGermGraph (ε (v ∘ Sum.inl)) (g (v ∘ Sum.inl))}

theorem jointCurveGermGraph_fiber {ρ κ : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) :
    projectionFiber (jointCurveGermGraph P ε g) p = curveGermGraph (ε p) (g p) := by
  ext v
  change (p ∈ P ∧ v ∈ curveGermGraph (ε p) (g p)) ↔ _
  exact and_iff_right hp

theorem jointCurveGermGraph_attach_definable {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ)
    (a : (ρ → ℝ) → κ → ℝ) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (hε : (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph P (fun p (_ : Unit) => ε p)))
    (ha : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a))
    (hf : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph (positiveTimeDomain P) f))
    (hpos : ∀ p ∈ P, 0 < ε p) :
    (univ : Set ℝ).Definable Language.ring
      (jointCurveGermGraph P ε (attachAtZero a f)) := by
  let B := ρ ⊕ (Unit ⊕ κ)
  let eA : ρ ⊕ κ → B := Sum.elim Sum.inl (fun k => Sum.inr (Sum.inr k))
  let eF : (ρ ⊕ Unit) ⊕ κ → B :=
    Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Sum.inl ()))) (fun k => Sum.inr (Sum.inr k))
  let eE : ρ ⊕ Unit → B ⊕ Unit := Sum.elim (fun p => Sum.inl (Sum.inl p)) Sum.inr
  have hz := (realPolynomial_zero_definable (MvPolynomial.X (Sum.inr (Sum.inl ()) : B))).inter
    (ha.preimage_comp eA)
  have hr := realDefinable_exists ((hε.preimage_comp eE).inter
    (realCoordinate_lt_definable (Sum.inl (Sum.inr (Sum.inl ())) : B ⊕ Unit) (Sum.inr ())))
  have h := hz.union ((hf.preimage_comp eF).inter hr)
  convert h using 1
  ext v
  have heA : v ∘ eA = Sum.elim (v ∘ Sum.inl) (fun k => v (Sum.inr (Sum.inr k))) := by
    funext i; cases i <;> rfl
  have heF : v ∘ eF = Sum.elim (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr (Sum.inl ()))))
      (fun k => v (Sum.inr (Sum.inr k))) := by
    funext i; rcases i with (i | ⟨⟩) | k <;> rfl
  have heE (r : Unit → ℝ) : Sum.elim v r ∘ eE = Sum.elim (v ∘ Sum.inl) r := by
    funext i; cases i <;> rfl
  simp only [mem_union, mem_inter_iff, mem_setOf_eq, mem_preimage,
    heA,heF,heE,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr]
  change (_ ∧ _ ∧ _) ↔
    (v (Sum.inr (Sum.inl ())) = 0 ∧
      ((v ∘ Sum.inl) ∈ P ∧ a (v ∘ Sum.inl) = (fun k => v (Sum.inr (Sum.inr k))))) ∨
    (((v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr (Sum.inl ()))) ∧
      f (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr (Sum.inl ())))) =
        (fun k => v (Sum.inr (Sum.inr k)))) ∧
      ∃ r : Unit → ℝ, (v ∘ Sum.inl ∈ P ∧ (fun _ : Unit => ε (v ∘ Sum.inl)) = r) ∧
        v (Sum.inr (Sum.inl ())) < r ())
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨hp,ht,hy⟩
    by_cases ht0 : v (Sum.inr (Sum.inl ())) = 0
    · left
      exact ⟨ht0,hp,by simpa only [attachAtZero,ht0,if_pos rfl] using hy.symm⟩
    · right
      have htPos := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      refine ⟨⟨⟨hp,htPos⟩,?_⟩,⟨fun _ => ε (v ∘ Sum.inl),⟨hp,rfl⟩,ht.2⟩⟩
      simpa only [attachAtZero,ht0,if_false] using hy.symm
  · rintro (⟨ht0,hp,hy⟩ | ⟨⟨⟨hp,htPos⟩,hy⟩,r,⟨_,hr⟩,htr⟩)
    · refine ⟨hp,⟨by rw [ht0],by simpa only [ht0] using hpos _ hp⟩,?_⟩
      simpa only [attachAtZero,ht0,if_pos rfl] using hy.symm
    · refine ⟨hp,⟨htPos.le,?_⟩,?_⟩
      · simpa only [← hr] using htr
      · simpa only [attachAtZero,ne_of_gt htPos,if_false] using hy.symm

/-- The curve and radius are chosen jointly before any parameter is fixed.
The only new external input is generic semialgebraic choice. -/
theorem published_joint_curve_selection
    (hChoice : PublishedSemialgebraicDefinableChoice)
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hC : HasPolynomialSignDescription C)
    (ha : HasPolynomialSignDescription (selectedFunctionGraph P a))
    (hcl : ∀ p ∈ P, a p ∈ closure (projectionFiber C p)) :
    ∃ (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ),
      HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)) ∧
      HasPolynomialSignDescription (jointCurveGermGraph P ε g) ∧
      ∀ p ∈ P, 0 < ε p ∧ ε p < 1 ∧ g p 0 = a p ∧
        ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p) := by
  have hP := hQE.finite_sign_description P (selectedFunctionGraph_domain_definable P a
    (hasPolynomialSignDescription_definable ha))
  obtain ⟨f,hf,hnear⟩ := published_joint_nearby_selector hChoice hQE P C a hC ha hcl
  obtain ⟨ε,hε,hr⟩ := published_joint_differentiable_radius hChoice hQE hNash P f hP hf
  refine ⟨ε,attachAtZero a f,hε,?_,?_⟩
  · exact hQE.finite_sign_description _ (jointCurveGermGraph_attach_definable P ε a f
      (hasPolynomialSignDescription_definable hε) (hasPolynomialSignDescription_definable ha)
      (hasPolynomialSignDescription_definable hf) (fun p hp => (hr p hp).1))
  · intro p hp
    refine ⟨(hr p hp).1,(hr p hp).2.1,attachAtZero_zero a f p,
      attachAtZero_continuousOn a f p (ε p) (fun t ht => (hnear p hp t ht).2)
        (hr p hp).2.2,?_⟩
    intro t ht
    rw [attachAtZero_positive a f p ht.1]
    exact (hnear p hp t ht.1).1

end PaperI
