import PaperILean.BoundedDistanceBands
import PaperILean.PublishedFormatComponents
import PaperILean.BufferedBandPreparedArc

/-! I1259: the original bounded-search projection has uniform sign format.
Bounds precede all input coefficients, box radii and widths. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance originalBandFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

theorem published_bounded_tuple_boundedBand_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (p : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (p i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image p) S → ∀ T W : ℝ,
      ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (planarBoundedBand S T W) := by
  classical
  have h := fun b : (Fin s → Bool × Bool) → Bool =>
    published_planarBoundedBandFamily_uniform_format hQE
      (universalPolynomialBooleanSet (Fin 2) s D b)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D b))
  choose sOut dOut hOut using h
  refine ⟨Finset.univ.sup sOut,Finset.univ.sup dOut,?_⟩
  intro p hp S hS T W
  obtain ⟨b,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D p hp S hS
  obtain ⟨B,hBc,hBd,hBS⟩ := hOut b (polynomialFamilyCoefficients D p) T W
  refine ⟨B,hBc.trans (Finset.le_sup (f:=sOut) (Finset.mem_univ b)),
    fun q hq => (hBd q hq).trans (Finset.le_sup (f:=dOut) (Finset.mem_univ b)),?_⟩
  simpa only [hEq,projectionFiber] using hBS

theorem published_bounded_sign_format_boundedBand_format
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ sOut dOut : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ q ∈ A, q.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ T W : ℝ, ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ sOut ∧
        (∀ q ∈ B, q.totalDegree ≤ dOut) ∧ PolynomialSignDetermined B (planarBoundedBand S T W) := by
  obtain ⟨sOut,dOut,h⟩ := published_bounded_tuple_boundedBand_format hQE s D
  refine ⟨sOut,dOut,?_⟩
  intro A S hc hd hS T W
  obtain ⟨p,hp,hSp⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact h p hp S hSp T W

theorem bounded_planar_set_exists_coordinateBox
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hE : Bornology.IsBounded E) :
    ∃ T : ℝ, 0 ≤ T ∧ (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T := by
  obtain ⟨T,hT,h⟩ := hE.exists_pos_norm_le
  refine ⟨T,hT.le,?_⟩
  rintro x ⟨y,hy,rfl⟩ j
  exact (PiLp.norm_apply_le y j).trans (h y hy)

theorem published_original_uniform_bufferedDistanceBand_format
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
  obtain ⟨sB,dB,h⟩ := published_bounded_sign_format_boundedBand_format hQE s D
  refine ⟨sB,dB,?_⟩
  intro E ho hb A hc hd hE W hW
  obtain ⟨T,hT,hbox⟩ := bounded_planar_set_exists_coordinateBox hb
  rw [bufferedDistanceBand_coordinates_eq_boundedBand hT hW ho hbox]
  exact h A _ hc hd hE T W


end PaperI
