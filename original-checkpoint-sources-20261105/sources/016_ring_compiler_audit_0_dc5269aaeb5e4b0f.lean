import PaperILean.RingQuantifierFreeMatrix

#print axioms PaperI.ringTermPolynomial
#print axioms PaperI.ringTermDegreeBound
#print axioms PaperI.ringTermPolynomial_eval
#print axioms PaperI.ringTermPolynomial_totalDegree_le
#print axioms PaperI.ringTermPolynomial_sub_eq_zero_iff
#print axioms PaperI.ringTermPolynomial_sub_totalDegree_le
#print axioms PaperI.ringFormulaAtomBound
#print axioms PaperI.ringFormulaDegreeBound
#print axioms PaperI.ringQFPolynomialFamily
#print axioms PaperI.ringBoundedFormulaSet
#print axioms PaperI.ringQFPolynomialFamily_card_le
#print axioms PaperI.ringQFPolynomialFamily_totalDegree_le
#print axioms PaperI.ringQFPolynomialFamily_signDetermined
#print axioms PaperI.ringQF_exists_polynomialBooleanSet
#print axioms PaperI.ringQF_exists_polynomialBoolean_realize

#check @PaperI.ringTermPolynomial
#check @PaperI.ringTermDegreeBound
#check @PaperI.ringTermPolynomial_eval
#check @PaperI.ringTermPolynomial_totalDegree_le
#check @PaperI.ringTermPolynomial_sub_eq_zero_iff
#check @PaperI.ringTermPolynomial_sub_totalDegree_le
#check @PaperI.ringFormulaAtomBound
#check @PaperI.ringFormulaDegreeBound
#check @PaperI.ringQFPolynomialFamily
#check @PaperI.ringBoundedFormulaSet
#check @PaperI.ringQFPolynomialFamily_card_le
#check @PaperI.ringQFPolynomialFamily_totalDegree_le
#check @PaperI.ringQFPolynomialFamily_signDetermined
#check @PaperI.ringQF_exists_polynomialBooleanSet
#check @PaperI.ringQF_exists_polynomialBoolean_realize

open FirstOrder PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
example (c x : ℝ) :
    MvPolynomial.eval (Sum.elim (fun _ : Unit => c) (fun _ : Unit => x))
      (ringTermPolynomial ((Language.Term.var (Sum.inl ()) : Language.ring.Term (Unit ⊕ Unit)) +
        Language.Term.var (Sum.inr ()))) = c + x := by
  rw [ringTermPolynomial_eval]
  simp
example : ringTermPolynomial ((Language.Term.var () : Language.ring.Term Unit) +
    -Language.Term.var ()) = 0 := by
  simp [ringTermPolynomial]
example : ringFormulaAtomBound (⊥ : Language.ring.BoundedFormula Empty 0) = 0 ∧
    ringFormulaDegreeBound (⊥ : Language.ring.BoundedFormula Empty 0) = 0 := by
  constructor <;> rfl
example : ringBoundedFormulaSet (⊥ : Language.ring.BoundedFormula Empty 0) = ∅ := rfl
example : ringBoundedFormulaSet (⊤ : Language.ring.BoundedFormula Empty 0) = Set.univ := by
  ext x
  simp [ringBoundedFormulaSet]
example (φ : Language.ring.BoundedFormula Unit 1) : ¬φ.ex.IsQF :=
  Language.BoundedFormula.not_ex_isQF φ
example (v : Unit → ℝ) (xs : Fin 1 → ℝ) :
    ((Language.Term.var (Sum.inl ()) : Language.ring.Term (Unit ⊕ Fin 1)).bdEqual
      (Language.Term.var (Sum.inr 0))).Realize v xs ↔ v () = xs 0 := Iff.rfl
example (c x : ℝ) :
    MvPolynomial.eval (Sum.elim (fun _ : Unit => c) (fun _ : Unit => x))
      (ringTermPolynomial ((Language.Term.var (Sum.inl ()) : Language.ring.Term (Unit ⊕ Unit)) *
        Language.Term.var (Sum.inr ()))) = c * x := by
  rw [ringTermPolynomial_eval]
  simp
