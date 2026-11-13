import PaperILean.PublishedSemialgebraicPaths

/-! The richer compatible semialgebraic chart input supplies the earlier
unmarked topological Hardt input. This avoids requiring two separate versions
of the same accepted theorem when applying monotonicity to a constructed path.
Pre-strategy evidence: checkpoint_108_path_pre_strategy.json. -/

noncomputable section
namespace PaperI

theorem PublishedCompatibleSemialgebraicHardtTriviality.toHardtTriviality
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality) :
    PublishedSemialgebraicHardtTriviality := by
  constructor
  intro ρ κ _ _ A hA hdom
  obtain ⟨D⟩ := hHardt.projection_trivialization A (fun _ => ∅) hA hdom
    (fun _ => ⟨∅, polynomialSignDetermined_empty⟩) (fun _ => Set.empty_subset _)
  exact ⟨D.toProjectionHardtData⟩

end PaperI
