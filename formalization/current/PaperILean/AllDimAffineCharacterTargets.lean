import PaperILean.AllDimDiagonalCharacter

/-! Exact contracts in the main theorem's finite-dimensional case of Lemma
2.1(i). The definitions assert no proof; GeneralAffineCharacter discharges them. -/

open Matrix

noncomputable section
namespace PaperI.AllDim

variable {n : ℕ}

def TranslationDeterminantStatement (n k : ℕ) : Prop :=
  ∀ c : (PhysicalSpace n),
    LinearMap.det (affineCoefficientMap n k c (1 : Matrix (Fin n) (Fin n) ℝ)) = 1

def CenteredLinearCharacterStatement (n k : ℕ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℝ,
    |LinearMap.det (affineCoefficientMap n k 0 B)| = |B.det| ^ chi n k

def AffineCharacterStatement (n k : ℕ) : Prop :=
  ∀ (c : (PhysicalSpace n)) (B : Matrix (Fin n) (Fin n) ℝ),
    |LinearMap.det (affineCoefficientMap n k c B)| = |B.det| ^ chi n k

theorem affineCoefficientMap_factor (n k : ℕ) (c : (PhysicalSpace n))
    (B : Matrix (Fin n) (Fin n) ℝ) :
    affineCoefficientMap n k c B = (affineCoefficientMap n k 0 B).comp
      (affineCoefficientMap n k c (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  apply LinearMap.ext
  intro F
  have h := affineCoefficientMap_comp n k c 0 (1 : Matrix (Fin n) (Fin n) ℝ) B F
  simpa only [Matrix.mulVec_zero, add_zero, Matrix.one_mul, LinearMap.comp_apply] using h.symm

/-- Conditional interface; both premises are proved in GeneralAffineCharacter. -/
theorem affineCharacter_of_translation_and_linear (n k : ℕ)
    (htranslation : TranslationDeterminantStatement n k)
    (hlinear : CenteredLinearCharacterStatement n k) : AffineCharacterStatement n k := by
  intro c B
  rw [affineCoefficientMap_factor, LinearMap.det_comp, htranslation c, mul_one]
  exact hlinear B

end PaperI.AllDim
