import PaperILean.PolynomialSignDefinability
import Mathlib.Topology.Homeomorph.Lemmas

/-! The projection-specialized structural content of BPR, second edition,
Theorem 5.46 (printed p. 185). The external input supplies a finite
semialgebraic partition and projection-compatible homeomorphisms. It does not
supply a measurable selection or a numerical component bound. The exact
projection image must itself be semialgebraic; callers establish that premise
from the separately named accepted QE input. Empty images admit zero pieces.
No compactness or nonempty ambient fiber space is assumed.

Executed pre-strategy cases: evidence/checkpoint_103_hardt_pre_strategy.json.
The structure has no supplied inhabitant; downstream implications retain the
explicit published-input parameter. -/

noncomputable section
namespace PaperI

/-- The actual image of the first-coordinate projection. -/
def projectionDomain {ι κ : Type*} (A : Set ((ι ⊕ κ) → ℝ)) : Set (ι → ℝ) :=
  {p | ∃ x : κ → ℝ, Sum.elim p x ∈ A}

/-- The actual fiber, with no closure or other modification. -/
def projectionFiber {ι κ : Type*} (A : Set ((ι ⊕ κ) → ℝ))
    (p : ι → ℝ) : Set (κ → ℝ) := {x | Sum.elim p x ∈ A}

/-- Hardt data on precisely the projection image. The homeomorphisms retain
both the original relation and the first-coordinate commuting identity. -/
structure ProjectionHardtData {ι κ : Type*} (A : Set ((ι ⊕ κ) → ℝ)) where
  n : ℕ
  piece : Fin n → Set (ι → ℝ)
  piece_semialgebraic : ∀ i, HasPolynomialSignDescription (piece i)
  piece_subset : ∀ i, piece i ⊆ projectionDomain A
  cover : ∀ p ∈ projectionDomain A, ∃ i, p ∈ piece i
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  basePoint : ∀ i, piece i
  fiber_semialgebraic : ∀ i,
    HasPolynomialSignDescription (projectionFiber A (basePoint i).val)
  chart : ∀ i, ((piece i) × (projectionFiber A (basePoint i).val)) ≃ₜ
    {z : (ι → ℝ) × (κ → ℝ) | z.1 ∈ piece i ∧ Sum.elim z.1 z.2 ∈ A}
  projection_chart : ∀ i y, (chart i y).val.1 = y.1.val

/-- Accepted projection instance of BPR 5.46. Only topological information
from the semialgebraic homeomorphisms is retained. The image-semialgebraicity
premise is explicit so that this contract does not hide a QE input. -/
structure PublishedSemialgebraicHardtTriviality : Prop where
  projection_trivialization : ∀ {ι κ : Type} [Finite ι] [Finite κ]
    (A : Set ((ι ⊕ κ) → ℝ)), HasPolynomialSignDescription A →
    HasPolynomialSignDescription (projectionDomain A) →
    Nonempty (ProjectionHardtData A)

namespace ProjectionHardtData
variable {ι κ : Type*} {A : Set ((ι ⊕ κ) → ℝ)} (D : ProjectionHardtData A)

/-- A reference point exists because every base piece lies in the actual image. -/
theorem referenceFiber_nonempty (i : Fin D.n) :
    (projectionFiber A (D.basePoint i).val).Nonempty :=
  D.piece_subset i (D.basePoint i).property

/-- Restrict a commuting Hardt chart to one exact fiber. -/
def fiberHomeomorph (i : Fin D.n) (p : D.piece i) :
    projectionFiber A (D.basePoint i).val ≃ₜ projectionFiber A p.val where
  toFun x := ⟨(D.chart i (p, x)).val.2, by
    have h := (D.chart i (p, x)).property.2
    rw [D.projection_chart] at h
    exact h⟩
  invFun x := ((D.chart i).symm ⟨(p.val, x.val), p.property, x.property⟩).2
  left_inv x := by
    have hz : (⟨(p.val, (D.chart i (p, x)).val.2), p.property, by
        simpa only [D.projection_chart] using (D.chart i (p, x)).property.2⟩ :
        {z : (ι → ℝ) × (κ → ℝ) | z.1 ∈ D.piece i ∧ Sum.elim z.1 z.2 ∈ A}) =
        D.chart i (p, x) := by
      apply Subtype.ext
      exact Prod.ext (D.projection_chart i (p, x)).symm rfl
    simp only [hz, Homeomorph.symm_apply_apply]
  right_inv x := by
    let z : {z : (ι → ℝ) × (κ → ℝ) |
        z.1 ∈ D.piece i ∧ Sum.elim z.1 z.2 ∈ A} :=
      ⟨(p.val, x.val), p.property, x.property⟩
    have hp : ((D.chart i).symm z).1 = p := by
      apply Subtype.ext
      have h := D.projection_chart i ((D.chart i).symm z)
      simpa only [Homeomorph.apply_symm_apply] using h.symm
    apply Subtype.ext
    change (D.chart i (p, ((D.chart i).symm z).2)).val.2 = x.val
    have hpair : (p, ((D.chart i).symm z).2) = (D.chart i).symm z :=
      Prod.ext hp.symm rfl
    rw [hpair, Homeomorph.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_snd.comp (continuous_subtype_val.comp
      ((D.chart i).continuous.comp (continuous_const.prodMk continuous_id)))
  continuous_invFun := by
    exact continuous_snd.comp ((D.chart i).symm.continuous.comp
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _))

/-- A fixed reference point gives a continuous local section; compatibility
with the projection is what ensures the point lies over the requested base. -/
theorem exists_continuous_piece_section (i : Fin D.n) :
    ∃ s : D.piece i → (κ → ℝ), Continuous s ∧
      ∀ p, Sum.elim p.val (s p) ∈ A := by
  obtain ⟨x, hx⟩ := D.referenceFiber_nonempty i
  refine ⟨fun p => (D.chart i (p, ⟨x, hx⟩)).val.2, ?_, ?_⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp
      ((D.chart i).continuous.comp (continuous_id.prodMk continuous_const)))
  · intro p
    have h := (D.chart i (p, ⟨x, hx⟩)).property.2
    rw [D.projection_chart] at h
    exact h

end ProjectionHardtData
end PaperI
