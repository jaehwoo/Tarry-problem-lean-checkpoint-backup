import PaperILean.PublishedScalarMonotonicity
namespace PaperI.Checkpoint106
example (f : ℝ → ℝ) {a b : ℝ} (h : b ≤ a) : openScalarGraph f a b = ∅ := by
  ext v
  simp only [openScalarGraph, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ha hb
  exact False.elim ((not_lt_of_ge h) (ha.trans hb))
example (f : ℝ → ℝ) (a : ℝ) : openScalarGraph f a a = ∅ := by
  ext v
  simp only [openScalarGraph, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha, hb, _⟩
  exact (lt_irrefl a) (ha.trans hb)
end PaperI.Checkpoint106
