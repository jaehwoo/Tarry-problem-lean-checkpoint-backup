import PaperILean.QuantitativeQEImpliesQualitative

#check PaperI.published_rawFormula_hasPolynomialSignDescription
#print axioms PaperI.published_rawFormula_hasPolynomialSignDescription
#check PaperI.published_definable_hasPolynomialSignDescription_of_quantitativeQE
#print axioms PaperI.published_definable_hasPolynomialSignDescription_of_quantitativeQE
#check PaperI.PublishedQuantitativeRealQE.toRealSemialgebraicity
#print axioms PaperI.PublishedQuantitativeRealQE.toRealSemialgebraicity

open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

-- Empty coordinate and false/true matrix boundaries are valid raw formulas.
example (h : PaperI.PublishedQuantitativeRealQE) :
    PaperI.HasPolynomialSignDescription
      {v : Fin 0 → ℝ | (⊥ : Language.ring.Formula (Fin 0)).Realize v} :=
  PaperI.published_rawFormula_hasPolynomialSignDescription h _

example (h : PaperI.PublishedQuantitativeRealQE) :
    PaperI.HasPolynomialSignDescription
      {v : Fin 0 → ℝ | (⊤ : Language.ring.Formula (Fin 0)).Realize v} :=
  PaperI.published_rawFormula_hasPolynomialSignDescription h _

-- Arbitrary real named constants are retained exactly; no algebraicity bound.
example (h : PaperI.PublishedQuantitativeRealQE) (c : ℝ) :
    PaperI.HasPolynomialSignDescription
      {v : Unit → ℝ | v () = c} := by
  have hd := PaperI.realPolynomial_zero_definable
    (MvPolynomial.X () - MvPolynomial.C c)
  have hs := PaperI.published_definable_hasPolynomialSignDescription_of_quantitativeQE
    h _ hd
  simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] using hs
