import PaperILean.QuantifiedPolynomialFormat
open PaperI
example : quantifierVariableCount [(true, 0), (false, 0)] = 0 := by rfl
example : ¬ ([(true, 0), (false, 0)] : QuantifierPrefix).length ≤
    quantifierVariableCount [(true, 0), (false, 0)] := by
  norm_num [quantifierVariableCount]
example : ([(true, 1), (false, 2)] : QuantifierPrefix).length ≤
    quantifierVariableCount [(true, 1), (false, 2)] := by
  norm_num [quantifierVariableCount]
example : ([] : QuantifierPrefix).length = quantifierVariableCount [] := rfl
