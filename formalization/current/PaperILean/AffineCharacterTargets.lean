import PaperILean.DiagonalCharacter

/-! Exact contracts in the main theorem's three-dimensional case of Lemma
2.1(i). The definitions assert no proof; GeneralAffineCharacter discharges them. -/

open Matrix

noncomputable section
namespace PaperI

def TranslationDeterminantStatement (k : ℕ) : Prop :=
  ∀ c : PhysicalSpace,
    LinearMap.det (affineCoefficientMap k c (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1

def CenteredLinearCharacterStatement (k : ℕ) : Prop :=
  ∀ B : Matrix (Fin 3) (Fin 3) ℝ,
    |LinearMap.det (affineCoefficientMap k 0 B)| = |B.det| ^ chi k

def AffineCharacterStatement (k : ℕ) : Prop :=
  ∀ (c : PhysicalSpace) (B : Matrix (Fin 3) (Fin 3) ℝ),
    |LinearMap.det (affineCoefficientMap k c B)| = |B.det| ^ chi k

theorem affineCoefficientMap_factor (k : ℕ) (c : PhysicalSpace)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    affineCoefficientMap k c B = (affineCoefficientMap k 0 B).comp
      (affineCoefficientMap k c (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  apply LinearMap.ext
  intro F
  have h := affineCoefficientMap_comp k c 0 (1 : Matrix (Fin 3) (Fin 3) ℝ) B F
  simpa only [Matrix.mulVec_zero, add_zero, Matrix.one_mul, LinearMap.comp_apply] using h.symm

/-- Conditional interface; both premises are proved in GeneralAffineCharacter. -/
theorem affineCharacter_of_translation_and_linear (k : ℕ)
    (htranslation : TranslationDeterminantStatement k)
    (hlinear : CenteredLinearCharacterStatement k) : AffineCharacterStatement k := by
  intro c B
  rw [affineCoefficientMap_factor, LinearMap.det_comp, htranslation c, mul_one]
  exact hlinear B

end PaperI
