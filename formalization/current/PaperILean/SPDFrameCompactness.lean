import PaperILean.FrameSublevelBounds
import PaperILean.FrameEnergyContinuity
import Mathlib.Topology.Order.Compact

/-! Compactness at Paper I 246. The ambient compact container has a positive
determinant floor, so singular matrices cannot be limit points of a sublevel.
The sublevel itself, not merely its closure, is proved compact. -/
noncomputable section
open scoped BigOperators Matrix Matrix.L2OpNorm
namespace PaperI

theorem isClosed_posSemidef_real {n : ℕ} :
    IsClosed {S : Matrix (Fin n) (Fin n) ℝ | S.PosSemidef} := by
  change IsClosed ({S : Matrix (Fin n) (Fin n) ℝ | S.IsHermitian} ∩
    {S | ∀ x : Fin n → ℝ, 0 ≤ dotProduct (star x) (S *ᵥ x)})
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop

def spdFrameCompactContainer (M : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {S | S.PosSemidef ∧ (Real.exp (-M / 2)) ^ 3 ≤ S.det ∧
    ∀ i j, |S i j| ≤ 3 * (1 + Real.sqrt M)}

theorem isClosed_spdFrameCompactContainer (M : ℝ) :
    IsClosed (spdFrameCompactContainer M) := by
  change IsClosed ({S : Matrix (Fin 3) (Fin 3) ℝ | S.PosSemidef} ∩
    ({S | (Real.exp (-M / 2)) ^ 3 ≤ S.det} ∩
      {S | ∀ i j, |S i j| ≤ 3 * (1 + Real.sqrt M)}))
  apply isClosed_posSemidef_real.inter
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_id.matrix_det
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_le (by fun_prop) continuous_const

theorem isCompact_spdFrameCompactContainer (M : ℝ) :
    IsCompact (spdFrameCompactContainer M) := by
  let C := 3 * (1 + Real.sqrt M)
  have hc : IsCompact (Set.Icc (fun _ _ : Fin 3 => -C) (fun _ _ : Fin 3 => C)) := isCompact_Icc
  apply hc.of_isClosed_subset (isClosed_spdFrameCompactContainer M)
  intro S hS
  constructor
  · intro i j
    exact (abs_le.mp (hS.2.2 i j)).1
  · intro i j
    exact (abs_le.mp (hS.2.2 i j)).2

theorem spdFrameCompactContainer_posDef (M : ℝ)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S ∈ spdFrameCompactContainer M) : S.PosDef :=
  posSemidef_posDef_of_det_ne_zero S hS.1
    (ne_of_gt ((pow_pos (Real.exp_pos _) 3).trans_le hS.2.1))

theorem FrameEnergy_sublevel_mem_container {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ)
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosDef) (hE : FrameEnergy F c lam S ≤ M) :
    S ∈ spdFrameCompactContainer M :=
  ⟨hS.posSemidef, FrameEnergy_sublevel_det_lower F c lam hlam S hS M hE,
    FrameEnergy_sublevel_entry_bounds F c lam hlam S hS M hE⟩

theorem FrameEnergy_posDef_sublevel_eq_container {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ) :
    {S : Matrix (Fin 3) (Fin 3) ℝ | S.PosDef ∧ FrameEnergy F c lam S ≤ M} =
      {S ∈ spdFrameCompactContainer M | FrameEnergy F c lam S ≤ M} := by
  ext S
  exact ⟨fun h => ⟨FrameEnergy_sublevel_mem_container F c lam hlam M S h.1 h.2, h.2⟩,
    fun h => ⟨spdFrameCompactContainer_posDef M S h.1, h.2⟩⟩

theorem isCompact_FrameEnergy_posDef_sublevel {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ) :
    IsCompact {S : Matrix (Fin 3) (Fin 3) ℝ | S.PosDef ∧ FrameEnergy F c lam S ≤ M} := by
  rw [FrameEnergy_posDef_sublevel_eq_container F c lam hlam M]
  apply (isCompact_spdFrameCompactContainer M).of_isClosed_subset
  · apply (isClosed_spdFrameCompactContainer M).isClosed_le
    · exact (continuousOn_FrameEnergy F c lam).mono
        (fun S hS => (spdFrameCompactContainer_posDef M S hS).det_pos)
    · exact continuousOn_const
  · exact fun _ h => h.1

theorem isCompact_FrameEnergy_symmetric_sublevel {k : ℕ} (F : CoefficientSpace k)
    (c : PhysicalSpace) (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ) :
    IsCompact {S : SymmetricMatrix 3 | (S : Matrix (Fin 3) (Fin 3) ℝ).PosDef ∧
      FrameEnergy F c lam S ≤ M} := by
  apply Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_FrameEnergy_posDef_sublevel F c lam hlam M)
  rintro S ⟨hS, _⟩
  exact ⟨symmetricMatrixOf S ((realMatrix_isHermitian_iff_isSymm S).mp hS.isHermitian), rfl⟩

end PaperI
