import PaperILean.DefinableDistanceBands
import PaperILean.PublishedFormatComponents
import PaperILean.BufferedBandPreparedArc

/-! I1259: fixed input sign format gives common output band format and a
common number of actual Euclidean connected components. Both constants are
chosen before E, its coefficients, W and the component seed. The sign format
of EACH INDIVIDUAL component is a separate remaining obligation. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance bandFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

theorem published_bounded_tuple_squaredBand_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (p : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S → ∀ W : ℝ,
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (planarSquaredBand S W) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_planarSquaredBandFamily_uniform_format hQE
      (universalPolynomialBooleanSet (Fin 2) s D b)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D b))
  choose sOut dOut hOut using h
  refine ⟨Finset.univ.sup sOut,Finset.univ.sup dOut,?_⟩
  intro p hp S hS W
  obtain ⟨b,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  obtain ⟨B,hBc,hBd,hBS⟩ := hOut b (polynomialFamilyCoefficients D p) W
  refine ⟨B,hBc.trans (Finset.le_sup (f:=sOut) (Finset.mem_univ b)),
    fun q hq => (hBd q hq).trans (Finset.le_sup (f:=dOut) (Finset.mem_univ b)),?_⟩
  simpa only [hEq,projectionFiber] using hBS

theorem published_bounded_sign_format_squaredBand_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ W : ℝ, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (planarSquaredBand S W) := by
  obtain ⟨sOut,dOut,h⟩ := published_bounded_tuple_squaredBand_format hQE s D
  refine ⟨sOut,dOut,?_⟩
  intro A S hc hd hS W
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp W

theorem published_uniform_bufferedDistanceBand_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sBand dBand : ℕ, ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))),
      IsOpen E → Bornology.IsBounded E →
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      ∀ W : ℝ, 0 < W → ∃ B : Finset (MvPolynomial (Fin 2) ℝ),
        B.card ≤ sBand ∧ (∀ q ∈ B, q.totalDegree ≤ dBand) ∧
        PolynomialSignDetermined B
          ((WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W) := by
  obtain ⟨sB,dB,h⟩ := published_bounded_sign_format_squaredBand_format hQE s D
  refine ⟨sB,dB,?_⟩
  intro E ho hb A hc hd hE W hW
  rw [bounded_bufferedDistanceBand_coordinates_eq_squaredBand ho hb hW]
  exact h A _ hc hd hE W

/-- This is a homeomorphism, not an isometry between Euclidean and sup norms. -/
def planarCoordinatesHomeomorph : WithLp 2 (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toEquiv := WithLp.equiv 2 (Fin 2 → ℝ)
  continuous_toFun := PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ)
  continuous_invFun := PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ)

/-- Actual components are transported, including seeds outside the band. -/
theorem bufferedBandCoordinates_eq_connectedComponentIn
    (E : Set (WithLp 2 (Fin 2 → ℝ))) (W : ℝ) (z : WithLp 2 (Fin 2 → ℝ)) :
    bufferedBandCoordinates E W z = connectedComponentIn
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W)
      ((WithLp.equiv 2 (Fin 2 → ℝ)) z) := by
  by_cases hz : z ∈ bufferedDistanceBand E W
  · exact planarCoordinatesHomeomorph.image_connectedComponentIn hz
  · have hz' : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∉
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W := by
      simpa using hz
    simp [bufferedBandCoordinates,bufferedBandComponent,
      connectedComponentIn_eq_empty hz,connectedComponentIn_eq_empty hz']

/-- M, sBand and dBand depend only on the INPUT format, before every
coefficient and width. Actual finiteness accompanies Nat.card. -/
theorem published_uniform_bufferedDistanceBand_format_and_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sBand dBand M : ℕ, ∀ (E : Set (WithLp 2 (Fin 2 → ℝ))),
      IsOpen E → Bornology.IsBounded E →
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)), A.card ≤ s →
      (∀ q ∈ A, q.totalDegree ≤ D) →
      PolynomialSignDetermined A ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) →
      ∀ W : ℝ, 0 < W →
      (∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sBand ∧
        (∀ q ∈ B, q.totalDegree ≤ dBand) ∧
        PolynomialSignDetermined B
          ((WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W)) ∧
      Finite (ConnectedComponents (bufferedDistanceBand E W)) ∧
      Nat.card (ConnectedComponents (bufferedDistanceBand E W)) ≤ M := by
  obtain ⟨sB,dB,hB⟩ := published_uniform_bufferedDistanceBand_format hQE s D
  obtain ⟨M,hM⟩ := published_bounded_sign_format_component_bound hCell hHardt hQE (Fin 2) sB dB
  refine ⟨sB,dB,M,?_⟩
  intro E ho hb A hc hd hE W hW
  obtain ⟨B,hBc,hBd,hBS⟩ := hB E ho hb A hc hd hE W hW
  refine ⟨⟨B,hBc,hBd,hBS⟩,?_⟩
  exact finite_connectedComponents_and_card_le_of_homeomorph
    (planarCoordinatesHomeomorph.image (bufferedDistanceBand E W)).symm
    (hM B _ hBc hBd hBS)

end PaperI
