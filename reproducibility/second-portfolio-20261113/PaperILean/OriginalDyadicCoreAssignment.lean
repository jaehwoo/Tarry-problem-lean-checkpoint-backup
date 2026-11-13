import PaperILean.JointComponentLabelAssignment
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Original I1259: half-open dyadic distance cores and the actual enlarged-band
component assignment. The same bounded-search graph is used throughout. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarBoundedCore (S : Set (Fin 2 → ℝ)) (T W : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∃ r : ℝ, Sum.elim (fun _ : Unit => r) x ∈
    planarBoundedSquaredDistanceGraph S T ∧ W ≤ r ∧ r < 2*W}

def planarBoundedCoreFamily {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set ((((ρ ⊕ Unit) ⊕ Unit) ⊕ Fin 2) → ℝ) :=
  {v | (fun i => v (Sum.inr i)) ∈ planarBoundedCore
    (projectionFiber G (fun i => v (Sum.inl (Sum.inl (Sum.inl i)))))
    (v (Sum.inl (Sum.inl (Sum.inr ())))) (v (Sum.inl (Sum.inr ())))}

theorem planarBoundedCore_subset_band (S : Set (Fin 2 → ℝ)) (T : ℝ)
    {W : ℝ} (hW : 0 < W) : planarBoundedCore S T W ⊆ planarBoundedBand S T W := by
  rintro x ⟨r,hr,hlo,hhi⟩
  exact ⟨r,hr,by linarith,by linarith⟩

theorem planarBoundedCoreFamily_definable {ρ : Type*} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (planarBoundedCoreFamily G) := by
  let β := ((ρ ⊕ Unit) ⊕ Unit) ⊕ Fin 2
  let e : ((ρ ⊕ Unit) ⊕ (Unit ⊕ Fin 2)) → β ⊕ Unit :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i)))
      (Sum.elim Sum.inr (fun i => Sum.inl (Sum.inr i)))
  let w : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ())))
  let r : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inr ())
  have h := realDefinable_exists
    (((planarBoundedSquaredDistanceGraphFamily_definable hG).preimage_comp e).inter
      ((realPolynomial_le_definable w r).inter (realPolynomial_lt_definable r (2*w))))
  convert h using 1
  ext v
  change (∃ a : ℝ, _ ∧ _ ∧ _) ↔ (∃ a : Unit → ℝ, _ ∧ _ ∧ _)
  simp only [mem_preimage,planarBoundedSquaredDistanceGraphFamily,mem_setOf_eq,
    Function.comp_def,e,Sum.elim_inl,Sum.elim_inr,w,r,MvPolynomial.eval_X,map_mul,map_ofNat]
  constructor
  · rintro ⟨a,ha,hl,hu⟩
    exact ⟨fun _ => a,ha,hl,hu⟩
  · rintro ⟨a,ha,hl,hu⟩
    refine ⟨a (),?_,hl,hu⟩
    convert ha using 1
    congr 1
    funext i
    cases i with
    | inl u => cases u; rfl
    | inr i => rfl

theorem planarBoundedCore_coordinates_iff {T W : ℝ} (hT : 0 ≤ T)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (z : WithLp 2 (Fin 2 → ℝ)) :
    (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ planarBoundedCore
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) T W ↔
      (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ planarCoordinateBox T ∧
        W ≤ Metric.infDist z Eᶜ ∧ Metric.infDist z Eᶜ < 2*W := by
  change (∃ r : ℝ, _ ∧ _ ∧ _) ↔ _
  rw [← planarBoxDistanceGraph_eq_boundedSquaredDistanceGraph ho hbox]
  constructor
  · rintro ⟨r,⟨_,hz,hr⟩,hl,hu⟩
    have heq : r = Metric.infDist z Eᶜ := by simpa only [Equiv.symm_apply_apply] using hr
    exact ⟨hz,heq ▸ hl,heq ▸ hu⟩
  · rintro ⟨hz,hl,hu⟩
    refine ⟨Metric.infDist z Eᶜ,⟨hT,hz,?_⟩,hl,hu⟩
    change Metric.infDist z Eᶜ = Metric.infDist
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ((WithLp.equiv 2 (Fin 2 → ℝ)) z)) Eᶜ
    rw [Equiv.symm_apply_apply]

theorem exists_dyadic_core {r : ℝ} (hr : 0 < r) :
    ∃ k : ℤ, (2:ℝ)^k ≤ r ∧ r < 2*(2:ℝ)^k := by
  obtain ⟨k,hl,hu⟩ := exists_mem_Ico_zpow hr (by norm_num : (1:ℝ)<2)
  refine ⟨k,hl,?_⟩
  simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one,mul_comm] using hu

theorem dyadic_core_unique {r : ℝ} {k l : ℤ}
    (hk : (2:ℝ)^k ≤ r ∧ r < 2*(2:ℝ)^k)
    (hl : (2:ℝ)^l ≤ r ∧ r < 2*(2:ℝ)^l) : k = l := by
  have no_lt : ∀ a b : ℤ, (2:ℝ)^a ≤ r → r < 2*(2:ℝ)^b → ¬ b < a := by
    intro a b ha hb hlt
    have hpow := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2)
      (show b+1≤a by omega)
    have hstep : (2:ℝ)^(b+1) = 2*(2:ℝ)^b := by
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one,mul_comm]
    rw [hstep] at hpow
    exact (not_lt_of_ge (hpow.trans ha)) hb
  exact le_antisymm (le_of_not_gt (no_lt k l hk.1 hl.2))
    (le_of_not_gt (no_lt l k hl.1 hk.2))

def originalDyadicComponentAssigned {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ) (k : ℤ) (i : Fin D.count) : Prop :=
  componentAssignedLabel D
    (fun ω j => active ω j ∧ point ω j ∈ planarBoundedCore
      (projectionFiber G (param ω)) (radius ω) ((2:ℝ)^k))
    (fun ω => Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k))
    point ω j i

theorem measurableSet_originalDyadicComponentAssigned {Ω Λ : Type*} {ρ : Type}
    [MeasurableSpace Ω] [Finite ρ]
    (hQE : PublishedRealSemialgebraicity)
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G)
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ)
    (ha : ∀ j, MeasurableSet {ω | active ω j})
    (hp : Measurable param) (hT : Measurable radius)
    (hx : ∀ j, Measurable (fun ω => point ω j))
    (j : Λ) (k : ℤ) (i : Fin D.count) :
    MeasurableSet {ω | originalDyadicComponentAssigned D active param radius point ω j k i} := by
  let q := fun ω => Sum.elim (Sum.elim (param ω) (fun _ : Unit => radius ω))
    (fun _ : Unit => (2:ℝ)^k)
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro a
    cases a with
    | inr u => exact measurable_const
    | inl a => cases a with
      | inl r => exact (measurable_pi_apply r).comp hp
      | inr u => exact hT
  apply measurableSet_componentAssignedLabel D _ q point _ hq hx
  intro label
  have hcore : MeasurableSet (planarBoundedCoreFamily G) := by
    have hsem : HasPolynomialSignDescription (planarBoundedCoreFamily G) :=
      hQE.finite_sign_description (planarBoundedCoreFamily G)
        (planarBoundedCoreFamily_definable (G := G) hG)
    simpa only [← BorelSpace.measurable_eq] using
      hasPolynomialSignDescription_borel hsem
  have hv : Measurable (fun ω => Sum.elim (q ω) (point ω label)) := by
    apply measurable_pi_lambda
    intro a
    cases a with
    | inl r => exact (measurable_pi_apply r).comp hq
    | inr r => exact (measurable_pi_apply r).comp (hx label)
  exact (ha label).inter (hcore.preimage hv)

theorem originalDyadicComponentAssigned_at_scale {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ) (k : ℤ) :
    (∃! i, originalDyadicComponentAssigned D active param radius point ω j k i) ↔
      active ω j ∧ point ω j ∈ planarBoundedCore
        (projectionFiber G (param ω)) (radius ω) ((2:ℝ)^k) := by
  apply componentAssignedLabel_exists_unique_iff
  intro w l hl
  exact planarBoundedCore_subset_band _ _ (zpow_pos (by norm_num : (0:ℝ)<2) k) hl.2

theorem originalDyadicComponentAssigned_count {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (k : ℤ) :
    Nat.card {i : Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j k i} ≤
      Nat.card (ConnectedComponents (planarBoundedBand
        (projectionFiber G (param ω)) (radius ω) ((2:ℝ)^k))) :=
  componentAssignedLabel_count_le_components D _ _ point ω

theorem originalDyadicComponentAssigned_exists_unique {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (z : WithLp 2 (Fin 2 → ℝ)) (hz : z ∈ E)
    (hpoint : point ω j = (WithLp.equiv 2 (Fin 2 → ℝ)) z)
    (ha : active ω j) (hr : 0 < Metric.infDist z Eᶜ) :
    ∃! q : ℤ × Fin D.count,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2 := by
  obtain ⟨k,hk⟩ := exists_dyadic_core hr
  have hc : point ω j ∈ planarBoundedCore (projectionFiber G (param ω)) (radius ω) ((2:ℝ)^k) := by
    rw [hpoint,← hE,planarBoundedCore_coordinates_iff hT ho hbox]
    exact ⟨hbox ⟨z,hz,rfl⟩,hk⟩
  obtain ⟨i,hi,huniq⟩ := (originalDyadicComponentAssigned_at_scale D active param radius point ω j k).mpr ⟨ha,hc⟩
  refine ⟨⟨k,i⟩,hi,?_⟩
  rintro ⟨l,t⟩ ht
  have hc' := ht.1.2
  rw [hpoint,← hE,planarBoundedCore_coordinates_iff hT ho hbox] at hc'
  have hlk : l = k := dyadic_core_unique hc'.2 hk
  subst l
  exact Prod.ext rfl (huniq t ht)

theorem originalDyadicComponentAssigned_actual_component {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (z : WithLp 2 (Fin 2 → ℝ))
    (hpoint : point ω j = (WithLp.equiv 2 (Fin 2 → ℝ)) z)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    projectionFiber (D.part i)
      (Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k)) =
      bufferedBandCoordinates E ((2:ℝ)^k) z := by
  apply originalJointBand_part_eq_component D _ hT
    (zpow_pos (by norm_num : (0:ℝ)<2) k) ho hE hbox i z
  rw [← hpoint]
  exact hj.2

theorem dyadic_core_buffer_lower {r δ : ℝ} {k : ℤ}
    (hδ : δ ≤ r) (hk : r < 2*(2:ℝ)^k) : δ/2 < (2:ℝ)^k := by
  linarith

theorem dyadic_core_index_bounds {r : ℝ} {lo hi k : ℤ}
    (hlow : (2:ℝ)^lo ≤ r) (hhigh : r < (2:ℝ)^(hi+1))
    (hk : (2:ℝ)^k ≤ r ∧ r < 2*(2:ℝ)^k) : lo ≤ k ∧ k ≤ hi := by
  constructor
  · by_contra h
    have hp := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2)
      (show k+1≤lo by omega)
    rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one] at hp
    have := hp.trans hlow
    nlinarith [hk.2]
  · by_contra h
    have hp := zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2)
      (show hi+1≤k by omega)
    exact (not_lt_of_ge (hp.trans hk.1)) hhigh

theorem originalDyadicComponentAssigned_finite_count {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (Q : Finset ℤ)
    (hQ : ∀ j k i, originalDyadicComponentAssigned D active param radius point ω j k i → k ∈ Q) :
    Finite {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ∧
    Nat.card {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ≤ Q.card * D.count := by
  let f : {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} → Q × Fin D.count :=
    fun q => (⟨q.val.1,by obtain ⟨j,hj⟩ := q.property; exact hQ j _ _ hj⟩,q.val.2)
  have hf : Function.Injective f := by
    intro q t hqt
    apply Subtype.ext
    exact Prod.ext (congrArg (fun v : Q × Fin D.count => v.1.val) hqt)
      (congrArg (fun v : Q × Fin D.count => v.2) hqt)
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans_eq (by simp)⟩

theorem exists_uniform_dyadic_core_window (δ U : ℝ) (hδ : 0 < δ) (hU : 0 < U) :
    ∃ lo hi : ℤ, ∀ r : ℝ, δ ≤ r → r ≤ U → ∀ k : ℤ,
      (2:ℝ)^k ≤ r → r < 2*(2:ℝ)^k → k ∈ Finset.Icc lo hi := by
  obtain ⟨lo,hlo⟩ := exists_dyadic_core hδ
  obtain ⟨hi,hhi⟩ := exists_dyadic_core hU
  refine ⟨lo,hi,?_⟩
  intro r hrδ hrU k hklo hkhi
  apply Finset.mem_Icc.mpr
  apply dyadic_core_index_bounds (hlo.1.trans hrδ) _ ⟨hklo,hkhi⟩
  have hu := hrU.trans_lt hhi.2
  simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one,mul_comm] using hu

theorem originalDyadicComponentAssigned_bounded_finite_count {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (δ U : ℝ) (hδ : 0 < δ) (hU : 0 < U)
    (hbound : ∀ j, active ω j →
      δ ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ ∧
      Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ ≤ U) :
    ∃ Q : Finset ℤ,
      (∀ j k i, originalDyadicComponentAssigned D active param radius point ω j k i → k ∈ Q) ∧
      Finite {q : ℤ × Fin D.count // ∃ j,
        originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ∧
      Nat.card {q : ℤ × Fin D.count // ∃ j,
        originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ≤ Q.card * D.count := by
  obtain ⟨lo,hi,hwindow⟩ := exists_uniform_dyadic_core_window δ U hδ hU
  have hQ : ∀ j k i, originalDyadicComponentAssigned D active param radius point ω j k i →
      k ∈ Finset.Icc lo hi := by
    intro j k i hj
    let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)
    have hc : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ planarBoundedCore
        ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) (radius ω) ((2:ℝ)^k) := by
      simpa only [z,Equiv.apply_symm_apply,hE] using hj.1.2
    have hρ := (planarBoundedCore_coordinates_iff hT ho hbox z).mp hc
    exact hwindow _ (hbound j hj.1.1).1 (hbound j hj.1.1).2 k hρ.2.1 hρ.2.2
  exact ⟨Finset.Icc lo hi,hQ,
    originalDyadicComponentAssigned_finite_count D active param radius point ω _ hQ⟩

end PaperI
