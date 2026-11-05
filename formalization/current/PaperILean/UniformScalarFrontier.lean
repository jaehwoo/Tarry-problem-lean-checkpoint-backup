import PaperILean.ActualDSections
import PaperILean.ScalarSemialgebraicFrontier108
import PaperILean.CompatibleHardtForMonotonicity

/-! Coefficient-uniform scalar frontier bounds for the actual parameter pieces.
The bound precedes the polynomials and the chosen Boolean combination. -/
noncomputable section
namespace PaperI
open Set

theorem bounded_scalar_frontier
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ S : Set (Unit → ℝ), HasBoundedSignFormat s D S →
      (frontier {t : ℝ | (fun _ : Unit => t) ∈ S}).Finite ∧
      Nat.card (frontier {t : ℝ | (fun _ : Unit => t) ∈ S}) ≤ K := by
  classical
  let B := (Fin s → Bool × Bool) → Bool
  have hex (b : B) := published_scalar_fiber_frontier_card_bound hCell hHardt hQE
    (universalPolynomialBooleanSet Unit s D b)
    (universalPolynomialBooleanSet_hasPolynomialSignDescription Unit s D b)
  choose K hK using hex
  refine ⟨Finset.univ.sup K, ?_⟩
  intro S hS
  obtain ⟨A,hc,hd,hA⟩ := hS
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hA
  obtain ⟨b,hb⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S
    (component_section_sign_image_decEq s _ _ p S hSp)
  have heq : {t : ℝ | (fun _ : Unit => t) ∈ S} =
      scalarProjectionFiber (universalPolynomialBooleanSet Unit s D b)
        (polynomialFamilyCoefficients D p) := by
    ext t
    rw [hb]
    rfl
  rw [heq]
  exact ⟨(hK b _).1, (hK b _).2.trans (Finset.le_sup (f := K) (Finset.mem_univ b))⟩

theorem bounded_fin1_scalar_frontier
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ K : ℕ, ∀ S : Set (Fin 1 → ℝ), HasBoundedSignFormat s D S →
      (frontier {t : ℝ | (fun _ : Fin 1 => t) ∈ S}).Finite ∧
      Nat.card (frontier {t : ℝ | (fun _ : Fin 1 => t) ∈ S}) ≤ K := by
  obtain ⟨K,hK⟩ := bounded_scalar_frontier hCell.toFiniteConnectedCover
    hHardt.toHardtTriviality hQE s D
  refine ⟨K,?_⟩
  intro S hS
  exact hK {x : Unit → ℝ | x ∘ (fun _ : Fin 1 => ()) ∈ S}
    (ActualDSections.bounded_sign_format_preimage_comp (fun _ : Fin 1 => ()) hS)

end PaperI
