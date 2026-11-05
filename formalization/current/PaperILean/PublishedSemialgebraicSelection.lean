import PaperILean.PublishedHardtTriviality
import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.FiniteBorelSectionAssembly

/-! The local Borel-selection argument in manuscript I, conditioning (iii).
The accepted inputs provide QE and the structural projection-compatible Hardt
charts. Choosing one actual reference-fiber point gives a continuous section
on each piece; finite measurable assembly supplies a section of the original
relation on its exact projection image. No global continuous section,
compactness, or extension off the actual projection image is asserted. -/

noncomputable section
namespace PaperI

/-- The topological and measurable application of Hardt data, independent of
any inhabitant of an external contract. -/
theorem ProjectionHardtData.exists_borel_section
    {ι κ : Type*} [Finite ι] [Finite κ] {A : Set ((ι ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) :
    ∃ σ : projectionDomain A → (κ → ℝ), Measurable σ ∧
      ∀ p, Sum.elim p.val (σ p) ∈ A := by
  classical
  choose s hs hR using D.exists_continuous_piece_section
  let U : Fin D.n → Set (projectionDomain A) := fun i => {p | p.val ∈ D.piece i}
  have hU (i : Fin D.n) : MeasurableSet (U i) := by
    have hb : MeasurableSet (D.piece i) := by
      convert hasPolynomialSignDescription_borel (D.piece_semialgebraic i)
      exact BorelSpace.measurable_eq
    exact measurable_subtype_coe hb
  have hcover (p : projectionDomain A) : ∃ i, p ∈ U i :=
    D.cover p.val p.property
  let t : ∀ i, U i → (κ → ℝ) := fun i p => s i ⟨p.val.val, p.property⟩
  have ht (i : Fin D.n) : Measurable (t i) := by
    apply Continuous.measurable
    exact (hs i).comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  exact exists_measurable_section_of_finite_cover U hU hcover t ht
    (fun p x => Sum.elim p.val x ∈ A) (fun i p => hR i ⟨p.val.val, p.property⟩)

/-- Borel selection with an already-established semialgebraic image. The
published input supplies structural trivializations rather than this conclusion. -/
theorem published_semialgebraic_borel_selection_of_sign_image
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A)
    (hD : HasPolynomialSignDescription (projectionDomain A)) :
    ∃ σ : projectionDomain A → (κ → ℝ), Measurable σ ∧
      ∀ p, Sum.elim p.val (σ p) ∈ A := by
  obtain ⟨D⟩ := hHardt.projection_trivialization A hA hD
  exact D.exists_borel_section

/-- Conditioning (iii), retaining the original semialgebraic relation and
actual projection domain. Finite coordinate types include zero coordinates;
empty projection images and empty fibers outside the image are allowed. -/
theorem published_semialgebraic_borel_selection
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A) :
    ∃ σ : projectionDomain A → (κ → ℝ), Measurable σ ∧
      ∀ p, Sum.elim p.val (σ p) ∈ A := by
  apply published_semialgebraic_borel_selection_of_sign_image hHardt A hA
  exact published_real_projection_has_sign_description hQE
    (hasPolynomialSignDescription_definable hA)

/-- If the relation takes values in a specified semialgebraic ambient subset,
the selector takes values in that actual subset, equipped with its induced
Borel measurable structure. The inclusion hypothesis is precisely A ⊆ Z × X
on the second coordinate; no extra regularity of the fibers is required. -/
theorem published_semialgebraic_borel_selection_into_subset
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)) (hA : HasPolynomialSignDescription A)
    (X : Set (κ → ℝ)) (hX : ∀ p x, Sum.elim p x ∈ A → x ∈ X) :
    ∃ σ : projectionDomain A → X, Measurable σ ∧
      ∀ p, Sum.elim p.val (σ p).val ∈ A := by
  obtain ⟨σ, hσ, hmem⟩ := published_semialgebraic_borel_selection hQE hHardt A hA
  exact ⟨fun p => ⟨σ p, hX p.val (σ p) (hmem p)⟩,
    hσ.subtype_mk, hmem⟩

end PaperI
