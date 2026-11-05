import PaperILean.CylindricalSelectedChainPaths

/-! The supplied sliced decomposition is now obtained from the existing
structural CAD input. The ambient relation and every fiber are unchanged. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadUnpackedRelation {ρ : Type} (n : ℕ) (S : Set ((ρ ⊕ Fin n) → ℝ)) :
    Set (CADVariables ρ n → ℝ) :=
  {z | Sum.elim (z ∘ cadBaseCoordinate n) (z ∘ cadOutputCoordinate n) ∈ S}

theorem cadUnpackedRelation_definable {ρ : Type} (n : ℕ) {S : Set ((ρ ⊕ Fin n) → ℝ)}
    (hS : (univ : Set ℝ).Definable Language.ring S) :
    (univ : Set ℝ).Definable Language.ring (cadUnpackedRelation n S) := by
  convert hS.preimage_comp (Sum.elim (cadBaseCoordinate n) (cadOutputCoordinate n)) using 1
  ext z
  have he : Sum.elim (z ∘ cadBaseCoordinate n) (z ∘ cadOutputCoordinate n) =
      z ∘ Sum.elim (cadBaseCoordinate n) (cadOutputCoordinate n) := by
    funext k; cases k <;> rfl
  change (Sum.elim (z ∘ cadBaseCoordinate n) (z ∘ cadOutputCoordinate n) ∈ S) ↔
    (z ∘ Sum.elim (cadBaseCoordinate n) (cadOutputCoordinate n)) ∈ S
  rw [he]

theorem cadPackedRelation_unpacked {ρ : Type} (n : ℕ) (S : Set ((ρ ⊕ Fin n) → ℝ)) :
    cadPackedRelation n (cadUnpackedRelation n S) = S := by
  ext v
  change (Sum.elim (cadPack n (v ∘ Sum.inl) (v ∘ Sum.inr) ∘ cadBaseCoordinate n)
    (cadPack n (v ∘ Sum.inl) (v ∘ Sum.inr) ∘ cadOutputCoordinate n) ∈ S) ↔ v ∈ S
  rw [cadPack_base,cadPack_output]
  have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    funext k; cases k <;> rfl
  rw [he]

theorem published_cylindrical_jointPath_sections
    (hCAD : PublishedCylindricalInitialBandDecomposition) (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (n : ℕ) (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin n) → ℝ))
    (x y : (ρ → ℝ) → Fin n → ℝ)
    (hP : HasPolynomialSignDescription P) (hS : HasPolynomialSignDescription S)
    (hX : HasPolynomialSignDescription (selectedFunctionGraph P x))
    (hY : HasPolynomialSignDescription (selectedFunctionGraph P y))
    (hconn : ∀ p ∈ P, IsPreconnected (projectionFiber S p))
    (hx : ∀ p ∈ P, x p ∈ projectionFiber S p)
    (hy : ∀ p ∈ P, y p ∈ projectionFiber S p) :
    Nonempty (JointSemialgebraicPath P S x y) := by
  have hE := hQE.finite_sign_description _
    (cadUnpackedRelation_definable n (hasPolynomialSignDescription_definable hS))
  obtain ⟨d⟩ := published_cylindrical_timeCylinder_decomposition hCAD hQE n P
    (cadUnpackedRelation n S) hP hE
  have he := cadPackedRelation_unpacked n S
  have h := published_cylindrical_selected_chain_jointPath hCAD hQE d P x y hP
    (fun _ hp => hp) hX hY (by simpa only [he] using hconn)
    (by simpa only [he] using hx) (by simpa only [he] using hy)
  simpa only [he] using h

end PaperI
