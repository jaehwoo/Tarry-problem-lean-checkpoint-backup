import PaperILean.DefinableLocalFrontier
import PaperILean.UniformDistanceBandFormat

/-! I1261: the local frontier has format controlled solely by input format.
The center and radius are parameters, not choices made before the bound. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance frontierFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

theorem published_bounded_tuple_localFrontier_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (p : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S → ∀ (z : Fin 2 → ℝ) (R : ℝ),
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧
        PolynomialSignDetermined B (planarLocalFrontier S z R) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_planarLocalFrontierFamily_uniform_format hQE
      (universalPolynomialBooleanSet (Fin 2) s D b)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D b))
  choose sOut dOut hOut using h
  refine ⟨Finset.univ.sup sOut, Finset.univ.sup dOut, ?_⟩
  intro p hp S hS z R
  obtain ⟨b, hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  obtain ⟨B, hBc, hBd, hBS⟩ := hOut b (polynomialFamilyCoefficients D p) z R
  refine ⟨B, hBc.trans (Finset.le_sup (f := sOut) (Finset.mem_univ b)),
    fun q hq => (hBd q hq).trans (Finset.le_sup (f := dOut) (Finset.mem_univ b)), ?_⟩
  simpa only [hEq, projectionFiber] using hBS

theorem published_bounded_sign_format_localFrontier_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (z : Fin 2 → ℝ) (R : ℝ), ∃ B : Finset (MvPolynomial (Fin 2) ℝ),
        B.card ≤ sOut ∧ (∀ q ∈ B, q.totalDegree ≤ dOut) ∧
        PolynomialSignDetermined B (planarLocalFrontier S z R) := by
  obtain ⟨sOut, dOut, h⟩ := published_bounded_tuple_localFrontier_format hQE s D
  refine ⟨sOut, dOut, ?_⟩
  intro A S hc hd hS z R
  obtain ⟨p, hp, hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp z R

end PaperI
