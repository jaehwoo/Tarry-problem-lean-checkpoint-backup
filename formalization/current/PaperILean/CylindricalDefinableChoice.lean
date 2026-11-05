import PaperILean.CylindricalJointSelector
import PaperILean.PublishedDefinableChoice

/-! Finite-coordinate transport of the constructed CAD selector. The choice
interface is proved from named structural CAD and qualitative QE inputs;
no new external contract or global inhabitant is assumed. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem published_cylindrical_selector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (R : Set ((ρ ⊕ κ) → ℝ))
    (hP : HasPolynomialSignDescription P) (hR : HasPolynomialSignDescription R)
    (hne : ∀ p ∈ P, ∃ x, Sum.elim p x ∈ R) :
    ∃ f : (ρ → ℝ) → κ → ℝ,
      HasPolynomialSignDescription (selectedFunctionGraph P f) ∧
      ∀ p ∈ P, Sum.elim p (f p) ∈ R := by
  letI : Fintype κ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let R' : Set ((ρ ⊕ Fin (Fintype.card κ)) → ℝ) :=
    {v | v ∘ Sum.map id e ∈ R}
  have hR' : HasPolynomialSignDescription R' :=
    hQE.finite_sign_description _ ((hasPolynomialSignDescription_definable hR).preimage_comp
      (Sum.map id e))
  have hne' : ∀ p ∈ P, ∃ x, Sum.elim p x ∈ R' := by
    intro p hp
    obtain ⟨x,hx⟩ := hne p hp
    refine ⟨x ∘ e.symm,?_⟩
    change (Sum.elim p (x ∘ e.symm)) ∘ Sum.map id e ∈ R
    convert hx using 1
    funext i
    cases i with
    | inl r => rfl
    | inr k => simp [Function.comp_def]
  obtain ⟨f,hf,hm⟩ := published_cylindrical_selector_fin hCAD hQE (Fintype.card κ) P R' hP hR' hne'
  refine ⟨fun p => f p ∘ e,hQE.finite_sign_description _
    (cad_selectedGraph_coordinates (hasPolynomialSignDescription_definable hf) e),?_⟩
  intro p hp
  have h := hm p hp
  change (Sum.elim p (f p)) ∘ Sum.map id e ∈ R at h
  convert h using 1
  funext i
  cases i <;> rfl

theorem PublishedCylindricalInitialBandDecomposition.toDefinableChoice
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) : PublishedSemialgebraicDefinableChoice := by
  constructor
  intro ρ κ _ _ R hR
  exact published_cylindrical_selector hCAD hQE (projectionDomain R) R
    (hQE.finite_sign_description _
      (realDefinable_exists (hasPolynomialSignDescription_definable hR))) hR (fun _ hp => hp)

end PaperI
