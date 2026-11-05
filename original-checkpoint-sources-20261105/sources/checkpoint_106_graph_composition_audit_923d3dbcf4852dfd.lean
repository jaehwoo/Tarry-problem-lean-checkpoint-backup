import PaperILean.PublishedGraphCompositionFormat

#check @PaperI.rawGraphComposition
#print axioms PaperI.rawGraphComposition

#check @PaperI.rawGraphComposition_realize
#print axioms PaperI.rawGraphComposition_realize

#check @PaperI.rawGraphCompositionParametric
#print axioms PaperI.rawGraphCompositionParametric

#check @PaperI.rawGraphCompositionParametric_realize
#print axioms PaperI.rawGraphCompositionParametric_realize

#check @PaperI.graphCompositionFiber
#print axioms PaperI.graphCompositionFiber

#check @PaperI.projectionFiber_rawGraphComposition
#print axioms PaperI.projectionFiber_rawGraphComposition

#check @PaperI.graphCompositionFiber_eq_partialGraph
#print axioms PaperI.graphCompositionFiber_eq_partialGraph

#check @PaperI.graphCompositionFiber_eq_graph_on_domain
#print axioms PaperI.graphCompositionFiber_eq_graph_on_domain

#check @PaperI.published_rawFormula_uniform_fiber_sign_format
#print axioms PaperI.published_rawFormula_uniform_fiber_sign_format

#check @PaperI.published_graphComposition_uniform_sign_format
#print axioms PaperI.published_graphComposition_uniform_sign_format

#check @PaperI.published_composed_partialGraph_uniform_sign_format
#print axioms PaperI.published_composed_partialGraph_uniform_sign_format

namespace PaperI.Checkpoint106
open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

-- Actual raw formulas must share the quantified intermediate coordinate.
private def zeroGraph : Language.ring.Formula ((Empty ⊕ Unit) ⊕ Unit) :=
  (Language.Term.var (Sum.inr ())).equal 0
private def oneGraph : Language.ring.Formula ((Empty ⊕ Unit) ⊕ Unit) :=
  (Language.Term.var (Sum.inl (Sum.inr ()))).equal 1

example (p : Empty → ℝ) (t z : Unit → ℝ) :
    ¬ (rawGraphComposition zeroGraph oneGraph).Realize (Sum.elim (Sum.elim p t) z) := by
  rw [rawGraphComposition_realize]
  simp only [zeroGraph, oneGraph, Language.Formula.realize_equal,
    Language.Term.realize_var, FirstOrder.Ring.realize_zero,
    FirstOrder.Ring.realize_one, Sum.elim_inr, Sum.elim_inl]
  rintro ⟨x, h0, h1⟩
  linarith

-- Zero intermediate coordinates: quantification over the unique empty tuple.
example (p : Empty → ℝ) (t z : Unit → ℝ) :
    (rawGraphComposition
      (⊤ : Language.ring.Formula ((Empty ⊕ Unit) ⊕ Fin 0))
      (⊤ : Language.ring.Formula ((Empty ⊕ Fin 0) ⊕ Unit))).Realize
        (Sum.elim (Sum.elim p t) z) := by
  rw [rawGraphComposition_realize]
  exact ⟨Fin.elim0, by simp⟩
end PaperI.Checkpoint106
