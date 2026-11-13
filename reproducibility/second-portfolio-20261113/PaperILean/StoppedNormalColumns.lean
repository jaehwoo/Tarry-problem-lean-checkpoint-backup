import PaperILean.StoppedTranslationNonconstant
import PaperILean.NormalColumnRepresentation
import PaperILean.NonconstantPolynomialProduct

/-! The qualitative normal-column conclusion of I683, with the manuscript's
augmented translation stop. The three columns are A,C,Tx in that order.
No quantitative lower bound or fourth-column rank conclusion is claimed. -/

noncomputable section
namespace PaperI

theorem stopped_normalOrbit_eq_zero {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S)
    (v : Fin 3 → ℝ) (hz : normalOrbitDifferential k S v = 0) : v = 0 := by
  by_cases hM : (fun i => S.2.2 i 0) = 0
  · have hG : ∀ c : ℝ,
        MvPolynomial.pderiv 0 (coefficientPolynomial S.1) ≠ MvPolynomial.C c :=
      stopped_pderiv_nonconstant hP S hstop 0 hM
    have hphase : (normalOrbitDifferential k S v).1 = 0 := congrArg Prod.fst hz
    have hprod := normalOrbit_phase_zero_implies_product_constant S v hphase
    apply (normalScalarPolynomial_eq_zero_iff v).mp
    exact zero_of_mul_eq_C_of_nonconstant _ _ hG _ hprod
  · apply normalOrbit_physical_zero_implies_eq_zero S hM v
    exact congrArg Prod.snd hz

theorem stopped_normalOrbit_ker_eq_bot {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    LinearMap.ker (normalOrbitDifferential k S) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  exact stopped_normalOrbit_eq_zero hP S hstop

theorem stopped_normalOrbit_injective {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    Function.Injective (normalOrbitDifferential k S) :=
  LinearMap.ker_eq_bot.mp (stopped_normalOrbit_ker_eq_bot hP S hstop)

theorem stopped_normalColumns_linearIndependent {k : ℕ} {P : ℝ} (hP : 0 < P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    LinearIndependent ℝ (fun j : Fin 3 => normalOrbitDifferential k S (Pi.single j 1)) := by
  exact (Pi.linearIndependent_single_one (Fin 3) ℝ).map' (normalOrbitDifferential k S)
    (stopped_normalOrbit_ker_eq_bot hP S hstop)

theorem stopped_normalOrbit_injective_of_two_le {k : ℕ} {P : ℝ} (hP : 2 ≤ P)
    (S : AugmentedState k) (hstop : AugmentedTranslationStopped P S) :
    Function.Injective (normalOrbitDifferential k S) :=
  stopped_normalOrbit_injective (lt_of_lt_of_le (by norm_num) hP) S hstop

end PaperI
