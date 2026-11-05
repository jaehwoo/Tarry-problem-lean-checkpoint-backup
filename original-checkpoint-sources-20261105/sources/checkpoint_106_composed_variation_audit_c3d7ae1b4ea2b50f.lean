import PaperILean.ComposedGraphVariation
#check @PaperI.scalarGraphCoordinates
#print axioms PaperI.scalarGraphCoordinates
#check @PaperI.composedScalarGraph
#print axioms PaperI.composedScalarGraph
#check @PaperI.composedScalarGraph_definable
#print axioms PaperI.composedScalarGraph_definable
#check @PaperI.composedScalarGraph_mem_iff
#print axioms PaperI.composedScalarGraph_mem_iff
#check @PaperI.composedScalarGraph_represents_on_Icc
#print axioms PaperI.composedScalarGraph_represents_on_Icc
#check @PaperI.published_composed_graph_common_partition_variation
#print axioms PaperI.published_composed_graph_common_partition_variation
example : PaperI.scalarGraphCoordinates (Sum.inl ()) = 0 := rfl
example : PaperI.scalarGraphCoordinates (Sum.inr ()) = 1 := rfl
example : PaperI.scalarGraphCoordinates.symm 0 = Sum.inl () := by decide
example : PaperI.scalarGraphCoordinates.symm 1 = Sum.inr () := by decide
