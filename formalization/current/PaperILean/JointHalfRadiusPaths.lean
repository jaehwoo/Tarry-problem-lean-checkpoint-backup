import PaperILean.JointCurveSelection
import PaperILean.JointUnitPathGraphs
import PaperILean.CurveGermRestriction

/-! The actual closed-unit path at the selected half-radius, jointly in p.
The radius is an actual semialgebraic section, not an independent parameter
silently specialized by a non-semialgebraic choice. Time-one evaluation gives
the actual interior endpoint section used by the next chart segment.
Pre-strategy evidence: checkpoint_116_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem jointUnitPathGraph_time_section {ρ κ : Type*}
    {P : Set (ρ → ℝ)} {g : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasPolynomialSignDescription (selectedFunctionGraph P (fun p => g p t)) := by
  let q : ρ ⊕ (Unit ⊕ κ) → MvPolynomial (ρ ⊕ κ) ℝ :=
    Sum.elim (fun r => MvPolynomial.X (Sum.inl r))
      (Sum.elim (fun _ => MvPolynomial.C t) (fun k => MvPolynomial.X (Sum.inr k)))
  have h := hasPolynomialSignDescription_polynomial_preimage hG q
  convert h using 1
  ext z
  simp only [selectedFunctionGraph,jointUnitPathGraph,unitPathGraph,mem_setOf_eq,
    Function.comp_def,q,Sum.elim_inl,Sum.elim_inr,MvPolynomial.eval_X,MvPolynomial.eval_C]
  simp only [ht,true_and,eq_comm]

def halfRadiusGraphRelation {ρ κ : Type*}
    (R : Set ((ρ ⊕ Unit) → ℝ)) (G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)) :
    Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  {z | ∃ r : ℝ, Sum.elim (z ∘ Sum.inl) (fun _ => r) ∈ R ∧
    Sum.elim (Sum.elim (z ∘ Sum.inl) (fun _ => r/2)) (z ∘ Sum.inr) ∈
      jointGermRescaledGraph G}

theorem halfRadiusGraphRelation_definable {ρ κ : Type} [Finite ρ] [Finite κ]
    {R : Set ((ρ ⊕ Unit) → ℝ)} {G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)}
    (hR : HasPolynomialSignDescription R) (hG : HasPolynomialSignDescription G) :
    (univ : Set ℝ).Definable Language.ring (halfRadiusGraphRelation R G) := by
  let δ := ρ ⊕ (Unit ⊕ κ)
  let eR : ρ ⊕ Unit → δ ⊕ Unit :=
    Sum.elim (fun r => Sum.inl (Sum.inl r)) Sum.inr
  let q : (ρ ⊕ Unit) ⊕ (Unit ⊕ κ) → MvPolynomial (δ ⊕ Unit) ℝ :=
    Sum.elim
      (Sum.elim (fun r => MvPolynomial.X (Sum.inl (Sum.inl r)))
        (fun _ => MvPolynomial.C (1/2 : ℝ) * MvPolynomial.X (Sum.inr ())))
      (fun k => MvPolynomial.X (Sum.inl (Sum.inr k)))
  have hQ := hasPolynomialSignDescription_polynomial_preimage
    (jointGermRescaledGraph_semialgebraic hG) q
  have h := realDefinable_exists
    (((hasPolynomialSignDescription_definable hR).preimage_comp eR).inter
      (hasPolynomialSignDescription_definable hQ))
  convert h using 1
  ext z
  have heR (w : Unit → ℝ) : Sum.elim z w ∘ eR =
      Sum.elim (z ∘ Sum.inl) (fun _ => w ()) := by
    funext i; rcases i with i | ⟨⟩ <;> rfl
  have heQ (w : Unit → ℝ) : (fun i => MvPolynomial.eval (Sum.elim z w) (q i)) =
      Sum.elim (Sum.elim (z ∘ Sum.inl) (fun _ => w ()/2)) (z ∘ Sum.inr) := by
    funext i
    rcases i with (i | ⟨⟩) | i
    · simp [q]
    · change MvPolynomial.eval (Sum.elim z w)
        (MvPolynomial.C (1/2 : ℝ) * MvPolynomial.X (Sum.inr ())) = w () / 2
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      simp only [Sum.elim_inr]
      ring
    · simp [q]
  change (∃ r : ℝ, _ ∧ _) ↔ ∃ w : Unit → ℝ, _ ∧ _
  simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,heR]
  constructor
  · rintro ⟨r,hr,hg⟩
    refine ⟨fun _ => r,hr,?_⟩
    change (fun i => MvPolynomial.eval (Sum.elim z (fun _ => r)) (q i)) ∈ _
    rw [heQ]
    exact hg
  · rintro ⟨w,hr,hg⟩
    refine ⟨w (),hr,?_⟩
    change (fun i => MvPolynomial.eval (Sum.elim z w) (q i)) ∈ _ at hg
    rw [heQ] at hg
    exact hg

def jointHalfRadiusPath {ρ κ : Type*} (ε : (ρ → ℝ) → ℝ)
    (g : (ρ → ℝ) → ℝ → κ → ℝ) (p : ρ → ℝ) : ℝ → κ → ℝ :=
  curveInitialSegment (g p) (ε p/2)

theorem jointHalfRadiusPath_joint_graph {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hε : ∀ p ∈ P, 0 < ε p) :
    jointUnitPathGraph P (jointHalfRadiusPath ε g) =
      halfRadiusGraphRelation (selectedFunctionGraph P (fun p (_ : Unit) => ε p))
        (jointCurveGermGraph P ε g) := by
  ext z
  let p := z ∘ Sum.inl
  change (p ∈ P ∧ z ∘ Sum.inr ∈ unitPathGraph (jointHalfRadiusPath ε g p)) ↔
    ∃ r : ℝ, (p ∈ P ∧ (fun _ : Unit => ε p) = (fun _ => r)) ∧ _
  constructor
  · rintro ⟨hp,hz⟩
    refine ⟨ε p,⟨hp,rfl⟩,?_⟩
    have hr : 0 ≤ ε p/2 := le_of_lt (half_pos (hε p hp))
    have hre : ε p/2 < ε p := by linarith [hε p hp]
    change z ∘ Sum.inr ∈ projectionFiber
      (jointGermRescaledGraph (halfOpenPathGraphFamily P ε g)) (Sum.elim p (fun _ => ε p/2))
    rw [halfOpenPathGraphFamily_rescaled_fiber P ε g hp hr hre]
    exact hz
  · rintro ⟨r,⟨hp,he⟩,hz⟩
    have he' : ε p = r := congrFun he ()
    subst r
    refine ⟨hp,?_⟩
    have hr : 0 ≤ ε p/2 := le_of_lt (half_pos (hε p hp))
    have hre : ε p/2 < ε p := by linarith [hε p hp]
    change z ∘ Sum.inr ∈ projectionFiber
      (jointGermRescaledGraph (halfOpenPathGraphFamily P ε g)) (Sum.elim p (fun _ => ε p/2)) at hz
    rw [halfOpenPathGraphFamily_rescaled_fiber P ε g hp hr hre] at hz
    exact hz

theorem published_jointHalfRadiusPath_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hε : ∀ p ∈ P, 0 < ε p)
    (hR : HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)))
    (hG : HasPolynomialSignDescription (jointCurveGermGraph P ε g)) :
    HasPolynomialSignDescription (jointUnitPathGraph P (jointHalfRadiusPath ε g)) := by
  rw [jointHalfRadiusPath_joint_graph P ε g hε]
  exact hQE.finite_sign_description _ (halfRadiusGraphRelation_definable hR hG)

theorem published_jointHalfRadiusEndpoint_semialgebraic
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hε : ∀ p ∈ P, 0 < ε p)
    (hR : HasPolynomialSignDescription (selectedFunctionGraph P (fun p (_ : Unit) => ε p)))
    (hG : HasPolynomialSignDescription (jointCurveGermGraph P ε g)) :
    HasPolynomialSignDescription (selectedFunctionGraph P (fun p => g p (ε p/2))) := by
  have h := jointUnitPathGraph_time_section
    (published_jointHalfRadiusPath_semialgebraic hQE P ε g hε hR hG) (t := 1) (by simp)
  simpa only [jointHalfRadiusPath,curveInitialSegment,mul_one] using h

theorem jointHalfRadiusPath_bounded_unitPaths {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (C : Set ((ρ ⊕ κ) → ℝ))
    (ε : (ρ → ℝ) → ℝ) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P (jointHalfRadiusPath ε g)))
    (h : ∀ p ∈ P, 0 < ε p ∧ ContinuousOn (g p) (Ico (0 : ℝ) (ε p)) ∧
      MapsTo (g p) (Ioo (0 : ℝ) (ε p)) (projectionFiber C p)) :
    ∃ s d : ℕ, ∀ p ∈ P, ∀ S : Set (κ → ℝ),
      g p 0 ∈ S → projectionFiber C p ⊆ S →
      ∃ γ : SemialgebraicUnitPath S (g p 0) (g p (ε p/2)),
        γ.toFun = jointHalfRadiusPath ε g p ∧ g p (ε p/2) ∈ projectionFiber C p ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ), A.card ≤ s ∧
          (∀ q ∈ A, q.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  obtain ⟨s,d,hfmt⟩ := jointUnitPathGraph_uniform_fiber_format P _ hG
  refine ⟨s,d,?_⟩
  intro p hp S h0 hCS
  obtain ⟨A,hs,hd,hA⟩ := hfmt p hp
  have hh := h p hp
  have hr : 0 < ε p/2 := half_pos hh.1
  have hre : ε p/2 < ε p := by linarith [hh.1]
  let γ : SemialgebraicUnitPath S (g p 0) (g p (ε p/2)) := {
    toFun := jointHalfRadiusPath ε g p
    continuousOn := curveInitialSegment_continuousOn hh.2.1 hr.le hre
    mapsTo := curveInitialSegment_mapsTo_ambient hh.2.2 hr hre h0 hCS
    source := curveInitialSegment_source _ _
    target := curveInitialSegment_target _ _
    semialgebraic := ⟨A,hA⟩ }
  exact ⟨γ,rfl,hh.2.2 ⟨hr,hre⟩,A,hs,hd,hA⟩

end PaperI
