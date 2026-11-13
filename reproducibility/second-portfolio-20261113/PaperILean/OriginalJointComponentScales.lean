import PaperILean.JointEuclideanDiameter
import PaperILean.OriginalDyadicCoreAssignment
import PaperILean.DyadicScaleRounding

/-! Original I1259/I1265: the diameter and L0 of the existing joint band
catalogue, followed by the already checked rounding. Empty fibers are kept;
all active values agree exactly with the original Euclidean component. -/
noncomputable section
namespace PaperI
open Set

theorem planarCoordinateBox_euclidean_isBounded (T : ℝ) :
    Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' planarCoordinateBox T) := by
  have he : planarCoordinateBox T = Icc (fun _ => -T) (fun _ => T) := by
    ext x
    simp only [planarCoordinateBox,mem_setOf_eq,mem_Icc,Pi.le_def,abs_le]
    exact forall_and
  rw [he]
  exact (isCompact_Icc.image (PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ))).isBounded

theorem originalJointBand_part_euclidean_isBounded {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) (i : Fin D.count) :
    Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber (D.part i) p) := by
  apply (planarCoordinateBox_euclidean_isBounded (p (Sum.inl (Sum.inr ())))).subset
  apply image_mono
  intro x hx
  exact planarBoundedBand_subset_box _ _ _ (D.subset p i hx)

def originalJointComponentScale {ρ : Type*} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) : ℝ :=
  max (p (Sum.inr ())) (planarFiberDiameter (D.part i) p)

theorem originalJointComponentScale_eq_of_empty {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) (he : projectionFiber (D.part i) p = ∅) :
    originalJointComponentScale D i p = max (p (Sum.inr ())) 0 := by
  rw [originalJointComponentScale,planarFiberDiameter_empty he]

theorem originalJointComponentScale_nonneg {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) : 0 ≤ originalJointComponentScale D i p :=
  (planarFiberDiameter_nonneg _ p).trans (le_max_right _ _)

theorem originalJointComponentScale_nonpos_width {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ρ → ℝ) (T : ℝ) {W : ℝ} (hW : W ≤ 0) :
    originalJointComponentScale D i
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) = 0 := by
  rw [originalJointComponentScale_eq_of_empty D i _
    (originalJointBand_nonpos_width_empty D p T hW i)]
  exact max_eq_right hW

theorem originalJointComponentDiameter_neg_radius {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ρ → ℝ) {T : ℝ} (hT : T < 0) (W : ℝ) :
    planarFiberDiameter (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) = 0 := by
  apply planarFiberDiameter_empty
  apply subset_empty_iff.mp
  have h := D.subset (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) i
  simpa only [planarBoundedBandFamily_fiber,
    planarBoundedBand_eq_empty_of_neg_radius _ hT W] using h

theorem originalJointComponentScale_pos {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) (hW : 0 < p (Sum.inr ())) :
    0 < originalJointComponentScale D i p := hW.trans_le (le_max_left _ _)

theorem published_originalJointComponentDiameter_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    Measurable (planarFiberDiameter (D.part i)) :=
  published_planarFiberDiameter_measurable hQE (D.semialgebraic i)
    (fun p => originalJointBand_part_euclidean_isBounded D p i)

theorem published_originalJointComponentScale_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    Measurable (originalJointComponentScale D i) :=
  (measurable_pi_apply (Sum.inr ())).max
    (published_originalJointComponentDiameter_measurable hQE D i)

theorem published_originalJointComponentBranches_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    MeasurableSet {p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ |
      planarFiberDiameter (D.part i) p ≤ p (Sum.inr ())} ∧
    MeasurableSet {p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ |
      p (Sum.inr ()) < planarFiberDiameter (D.part i) p} := by
  exact ⟨measurableSet_le (published_originalJointComponentDiameter_measurable hQE D i)
    (measurable_pi_apply (Sum.inr ())),
    measurableSet_lt (measurable_pi_apply (Sum.inr ()))
      (published_originalJointComponentDiameter_measurable hQE D i)⟩

theorem originalJointComponentDiameter_eq {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (i : Fin D.count) (z : WithLp 2 (Fin 2 → ℝ))
    (hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))) :
    planarFiberDiameter (D.part i) (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) =
      Metric.diam (bufferedBandComponent E W z) := by
  rw [planarFiberDiameter,originalJointBand_part_eq_component D p hT hW ho hE hbox i z hz,
    bufferedBandCoordinates_euclidean_image]

theorem originalJointComponentScale_eq {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (i : Fin D.count) (z : WithLp 2 (Fin 2 → ℝ))
    (hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))) :
    originalJointComponentScale D i (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) =
      bufferedComponentScale E W z := by
  unfold originalJointComponentScale bufferedComponentScale
  rw [originalJointComponentDiameter_eq D p hT hW ho hE hbox i z hz]
  rfl

theorem published_originalJointRoundedScales_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    Measurable (fun p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ =>
      (roundedDyadicScale (originalJointComponentScale D i p),
        roundedDyadicScale (p (Sum.inr ())))) :=
  (roundedDyadicScale_measurable.comp
    (published_originalJointComponentScale_measurable hQE D i)).prodMk
    (roundedDyadicScale_measurable.comp (measurable_pi_apply (Sum.inr ())))

theorem originalJointRoundedScales_order {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) :
    1 ≤ roundedDyadicScale (p (Sum.inr ())) ∧
      roundedDyadicScale (p (Sum.inr ())) ≤
        roundedDyadicScale (originalJointComponentScale D i p) :=
  ⟨one_le_roundedDyadicScale _,roundedDyadicScale_mono (le_max_left _ _)⟩

/-- The same exponent is chosen before the catalogue, coefficient valuation,
P, q and scales. This is the existing rounding comparison, unchanged. -/
theorem originalJointRoundedScales_uniform_comparison (c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, ∀ (ρ : Type) (G : Set ((ρ ⊕ Fin 2) → ℝ))
      (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
      (p : ((ρ ⊕ Unit) ⊕ Unit) → ℝ) (P : ℝ) (q : ℕ), 2 ≤ P →
      c*(P^q)⁻¹ ≤ p (Sum.inr ()) →
      (0 < p (Sum.inr ()) ∧ p (Sum.inr ()) ≤ roundedDyadicScale (p (Sum.inr ())) ∧
        roundedDyadicScale (p (Sum.inr ())) ≤ P^(m+q+1)*p (Sum.inr ())) ∧
      (0 < originalJointComponentScale D i p ∧
        originalJointComponentScale D i p ≤ roundedDyadicScale (originalJointComponentScale D i p) ∧
        roundedDyadicScale (originalJointComponentScale D i p) ≤
          P^(m+q+1)*originalJointComponentScale D i p) := by
  obtain ⟨m,hm⟩ := uniform_roundedDyadicScale_power_comparison c hc
  refine ⟨m,?_⟩
  intro ρ G D i p P q hP hW
  exact ⟨hm P q hP _ hW,hm P q hP _ (hW.trans (le_max_left _ _))⟩

/-- Compose with arbitrary measurable original coefficient/radius data.
The index is fixed from the existing finite catalogue, not chosen per label. -/
theorem published_originalDyadicComponentScales_measurable
    (hQE : PublishedRealSemialgebraicity) {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (hp : Measurable param) (hT : Measurable radius) (k : ℤ) (i : Fin D.count) :
    Measurable (fun ω =>
      (roundedDyadicScale (originalJointComponentScale D i
        (Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k))),
        roundedDyadicScale ((2:ℝ)^k))) := by
  apply (published_originalJointRoundedScales_measurable hQE D i).comp
  apply measurable_pi_lambda
  intro a
  cases a with
  | inr u => exact measurable_const
  | inl a => cases a with
    | inl r => exact (measurable_pi_apply r).comp hp
    | inr u => exact hT

theorem originalDyadicComponentAssigned_scale_eq {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ} {i : Fin D.count}
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    (z : WithLp 2 (Fin 2 → ℝ))
    (hpoint : point ω j = (WithLp.equiv 2 (Fin 2 → ℝ)) z)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    originalJointComponentScale D i
      (Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k)) =
      bufferedComponentScale E ((2:ℝ)^k) z := by
  unfold originalJointComponentScale planarFiberDiameter bufferedComponentScale
  rw [originalDyadicComponentAssigned_actual_component D active param radius point
    ho hT hE hbox z hpoint hj,bufferedBandCoordinates_euclidean_image]
  rfl

end PaperI
