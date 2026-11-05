import PaperILean.BoundedQuantifiedFormat

#print axioms PaperI.QuantifierPrefix
#print axioms PaperI.quantifierVariableCount
#print axioms PaperI.realizeQuantifierPrefix
#print axioms PaperI.polynomialPrenexSet
#print axioms PaperI.realizeQuantifierPrefix_nil
#print axioms PaperI.realizeQuantifierPrefix_forall
#print axioms PaperI.realizeQuantifierPrefix_exists
#print axioms PaperI.realizeQuantifierPrefix_congr
#print axioms PaperI.realizeQuantifierPrefix_zero_block
#print axioms PaperI.realizeQuantifierPrefix_const
#print axioms PaperI.polynomialPrenexSet_congr_matrix
#print axioms PaperI.polynomialPrenexSet_true
#print axioms PaperI.polynomialPrenexSet_false
#print axioms PaperI.PublishedQuantitativeRealQE
#print axioms PaperI.PublishedQuantitativeRealQE.mk
#print axioms PaperI.PublishedQuantitativeRealQE.output_format
#print axioms PaperI.published_quantified_polynomial_sign_format
#print axioms PaperI.published_polynomialPrenexSet_hasPolynomialSignDescription
#print axioms PaperI.QuantifierPrefixCode
#print axioms PaperI.quantifierPrefixDecode
#print axioms PaperI.quantifierBlock_size_le_total
#print axioms PaperI.quantifierPrefixEncode
#print axioms PaperI.quantifierPrefix_decode_encode
#print axioms PaperI.published_bounded_quantified_polynomial_sign_format
#print axioms PaperI.published_at_most_quantified_polynomial_sign_format

#check @PaperI.QuantifierPrefix
#check @PaperI.quantifierVariableCount
#check @PaperI.realizeQuantifierPrefix
#check @PaperI.polynomialPrenexSet
#check @PaperI.realizeQuantifierPrefix_nil
#check @PaperI.realizeQuantifierPrefix_forall
#check @PaperI.realizeQuantifierPrefix_exists
#check @PaperI.realizeQuantifierPrefix_congr
#check @PaperI.realizeQuantifierPrefix_zero_block
#check @PaperI.realizeQuantifierPrefix_const
#check @PaperI.polynomialPrenexSet_congr_matrix
#check @PaperI.polynomialPrenexSet_true
#check @PaperI.polynomialPrenexSet_false
#check @PaperI.PublishedQuantitativeRealQE
#check @PaperI.PublishedQuantitativeRealQE.mk
#check @PaperI.PublishedQuantitativeRealQE.output_format
#check @PaperI.published_quantified_polynomial_sign_format
#check @PaperI.published_polynomialPrenexSet_hasPolynomialSignDescription
#check @PaperI.QuantifierPrefixCode
#check @PaperI.quantifierPrefixDecode
#check @PaperI.quantifierBlock_size_le_total
#check @PaperI.quantifierPrefixEncode
#check @PaperI.quantifierPrefix_decode_encode
#check @PaperI.published_bounded_quantified_polynomial_sign_format
#check @PaperI.published_at_most_quantified_polynomial_sign_format

open PaperI
example : quantifierVariableCount [(true, 0), (false, 2), (true, 0)] = 2 := by decide
example : realizeQuantifierPrefix [(true, 1), (false, 1)]
    (fun v => v ⟨0, by decide⟩ = v ⟨1, by decide⟩) := by
  intro x
  refine ⟨x, ?_⟩
  simp [realizeQuantifierPrefix, Fin.append, Fin.addCases]
example : ¬realizeQuantifierPrefix [(false, 1), (true, 1)]
    (fun v => v ⟨0, by decide⟩ = v ⟨1, by decide⟩) := by
  rintro ⟨x, hx⟩
  have h := hx (fun _ => x 0 + 1)
  simp [realizeQuantifierPrefix, Fin.append, Fin.addCases] at h
example {α : Type} (blocks : QuantifierPrefix) :
    polynomialPrenexSet (α := α) blocks (fun _ : Fin 1 => 0)
      (fun bits => (bits 0).1) = Set.univ := by
  ext x
  simp [polynomialPrenexSet, polynomialBooleanSet, polynomialFamilySignCode,
    realizeQuantifierPrefix_const]
example (blocks : QuantifierPrefix) :
    polynomialPrenexSet (α := Fin 0) blocks (fun _ : Fin 0 => 0)
      (fun _ => false) = ∅ := polynomialPrenexSet_false _ _
example : (List.replicate 8 (true, 0)).length = 8 ∧
    quantifierVariableCount (List.replicate 8 (true, 0)) = 0 := by decide
