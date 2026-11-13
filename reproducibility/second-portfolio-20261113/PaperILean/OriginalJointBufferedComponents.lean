import PaperILean.JointSemialgebraicComponents
import PaperILean.OriginalUniformDistanceBandFormat
import PaperILean.UniformDistanceBandFormat

/-! I1259/I1265: the actual original bounded-search band, jointly in input
coefficients, box radius, and width. No new external contract is assumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_original_joint_buffered_components
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    Nonempty (JointComponentPartition (planarBoundedBandFamily G)) :=
  published_joint_component_partition hCell hHardt hQE _
    (hQE.finite_sign_description _ (planarBoundedBandFamily_definable hG))

theorem published_uniform_original_joint_buffered_components
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s d : ℕ) :
    ∃ M : ℕ, ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition
        (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count ≤ M := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_original_joint_buffered_components hCell hHardt hQE
      (universalPolynomialBooleanSet (Fin 2) s d b)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s d b))
  let D := fun b => Classical.choice (h b)
  exact ⟨Finset.univ.sup (fun b => (D b).count),fun b =>
    ⟨D b,Finset.le_sup (f := fun b => (D b).count) (Finset.mem_univ b)⟩⟩

theorem originalJointBand_fiber_eq {ρ : Type*}
    (G : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) {T W : ℝ}
    (hT : 0 ≤ T) (hW : 0 < W) {E : Set (WithLp 2 (Fin 2 → ℝ))}
    (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T) :
    projectionFiber (planarBoundedBandFamily G)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) =
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W := by
  rw [planarBoundedBandFamily_fiber,← hE]
  exact (bufferedDistanceBand_coordinates_eq_boundedBand hT hW ho hbox).symm

theorem originalJointBand_part_eq_component {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (i : Fin D.count) (z : WithLp 2 (Fin 2 → ℝ))
    (hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))) :
    projectionFiber (D.part i) (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) =
      bufferedBandCoordinates E W z := by
  rw [D.component _ i _ hz,originalJointBand_fiber_eq G p hT hW ho hE hbox,
    ← bufferedBandCoordinates_eq_connectedComponentIn]

theorem originalJointBand_core_covered {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (z : WithLp 2 (Fin 2 → ℝ))
    (hzlo : W ≤ Metric.infDist z Eᶜ) (hzhi : Metric.infDist z Eᶜ < 2*W) :
    ∃ i : Fin D.count, (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ projectionFiber (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) := by
  apply D.cover
  rw [originalJointBand_fiber_eq G p hT hW ho hE hbox]
  refine ⟨z,?_,rfl⟩
  change W/2 < Metric.infDist z Eᶜ ∧ Metric.infDist z Eᶜ < 4*W
  constructor <;> linarith

theorem originalJointBand_nonpos_width_empty {ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (p : ρ → ℝ) (T : ℝ) {W : ℝ} (hW : W ≤ 0) (i : Fin D.count) :
    projectionFiber (D.part i) (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) = ∅ := by
  apply subset_empty_iff.mp
  have h := D.subset (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) i
  simpa only [planarBoundedBandFamily_fiber,planarBoundedBand_eq_empty_of_nonpos_width _ _ hW] using h

end PaperI
