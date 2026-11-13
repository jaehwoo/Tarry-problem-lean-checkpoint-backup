import PaperILean.RotationHaarVolume
import PaperILean.FiniteMeasurePacking

/-! I311-315,331: a coefficient-independent finite SO(3) orientation packing.
The exact unchanged U_E is used, with packing radius theta/4 and cover radius
theta. No finite maximal family or reciprocal-volume bound is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix Matrix.L2OpNorm
namespace PaperI

def rotationNeighborhoodTranslate (E : PositiveFrame) (t : ℝ) (O : rotationGroup3) :
    Set rotationGroup3 := (fun P => O * P) '' rotationNeighborhood E t

theorem rotationNeighborhoodTranslate_measurableSet (E : PositiveFrame) (t : ℝ)
    (O : rotationGroup3) : MeasurableSet (rotationNeighborhoodTranslate E t O) :=
  (MeasurableEquiv.mulLeft O).measurableSet_image.mpr (rotationNeighborhood_measurableSet E t)

theorem rotationNeighborhoodTranslate_measure (E : PositiveFrame) (t : ℝ)
    (O : rotationGroup3) : rotationHaarMeasure (rotationNeighborhoodTranslate E t O) =
      rotationHaarMeasure (rotationNeighborhood E t) :=
  measure_smul rotationHaarMeasure O (rotationNeighborhood E t)

theorem self_mem_rotationNeighborhoodTranslate (E : PositiveFrame) (t : ℝ)
    (ht : 0 < t) (O : rotationGroup3) : O ∈ rotationNeighborhoodTranslate E t O :=
  ⟨1, (one_mem_rotationNeighborhood_iff E t).mpr ht, mul_one O⟩

theorem rotationNeighborhood_relative_of_translate_intersection
    (E : PositiveFrame) (t : ℝ) (ht : t < 1) (O P : rotationGroup3)
    (h : ¬ Disjoint (rotationNeighborhoodTranslate E t O) (rotationNeighborhoodTranslate E t P)) :
    O⁻¹ * P ∈ rotationNeighborhood E (2 * t / (1-t)) := by
  obtain ⟨x, ⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩ := Set.not_disjoint_iff.mp h
  exact rotationNeighborhood_relative_of_left_intersection E t ht O P u v hu hv
    (hux.trans hvx.symm)

theorem rotationNeighborhood_packing_separated (E : PositiveFrame) (t : ℝ) (ht : 0 < t)
    (s : Finset rotationGroup3) (hs : (↑s : Set rotationGroup3).PairwiseDisjoint
      (rotationNeighborhoodTranslate E t)) (O P : rotationGroup3)
    (hO : O ∈ s) (hP : P ∈ s) (hne : O ≠ P) :
    t ≤ ‖frameConjugate E (rotationMatrix (O⁻¹ * P) - 1)‖ := by
  apply le_of_not_gt
  intro hsmall
  have hPleft : P ∈ rotationNeighborhoodTranslate E t O :=
    ⟨O⁻¹ * P, hsmall, mul_inv_cancel_left O P⟩
  exact (Set.disjoint_left.mp (hs hO hP hne)) hPleft
    (self_mem_rotationNeighborhoodTranslate E t ht P)

theorem rotationNeighborhood_exists_maximal_packing (E : PositiveFrame) (t : ℝ)
    (ht : 0 < t) :
    ∃ s : Finset rotationGroup3,
      (↑s : Set rotationGroup3).PairwiseDisjoint (rotationNeighborhoodTranslate E t) ∧
      (s.card : ℝ) ≤ 1 / (rotationHaarMeasure (rotationNeighborhood E t)).toReal ∧
      (∀ r : Finset rotationGroup3,
        (↑r : Set rotationGroup3).PairwiseDisjoint (rotationNeighborhoodTranslate E t) →
          r.card ≤ s.card) ∧
      ∀ O, ∃ P ∈ s, ¬ Disjoint (rotationNeighborhoodTranslate E t O)
        (rotationNeighborhoodTranslate E t P) := by
  have hm : 0 < (rotationHaarMeasure (rotationNeighborhood E t)).toReal :=
    ENNReal.toReal_pos (rotationHaarMeasure_neighborhood_positive E t ht).ne'
      (rotationHaarMeasure_neighborhood_finite E t).ne
  apply finiteMeasurePacking_exists rotationHaarMeasure (rotationNeighborhoodTranslate E t)
    (rotationNeighborhoodTranslate_measurableSet E t) _ hm
  intro O
  change (rotationHaarMeasure (rotationNeighborhoodTranslate E t O)).toReal = _
  rw [rotationNeighborhoodTranslate_measure]

theorem rotationOrientationNet_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i),
      e 0 ≤ e 1 → e 1 ≤ e 2 → ∀ θ : ℝ, 0 < θ → θ < 1/10 →
        ∃ s : Finset rotationGroup3,
          (↑s : Set rotationGroup3).PairwiseDisjoint
            (rotationNeighborhoodTranslate (positiveDiagonalFrame e he) (θ/4)) ∧
          (s.card : ℝ) ≤ (C / θ^3) * (e 2 / e 0)^2 ∧
          (∀ r : Finset rotationGroup3,
            (↑r : Set rotationGroup3).PairwiseDisjoint
              (rotationNeighborhoodTranslate (positiveDiagonalFrame e he) (θ/4)) →
                r.card ≤ s.card) ∧
          (∀ O : rotationGroup3, ∃ P ∈ s,
            P⁻¹ * O ∈ rotationNeighborhood (positiveDiagonalFrame e he) θ) ∧
          (∀ O ∈ s, ∀ P ∈ s, O ≠ P →
            θ/4 ≤ ‖diagonalFrameConjugate e (rotationMatrix (O⁻¹ * P) - 1)‖) := by
  obtain ⟨C, hC, hrec⟩ := rotationHaarMeasure_diagonal_neighborhood_reciprocal_bound
  refine ⟨64*C, by positivity, ?_⟩
  intro e he h01 h12 θ hθ0 hθ
  have hq0 : 0 < θ/4 := by positivity
  have hqsmall : θ/4 < 1/10 := by linarith
  have hq1 : θ/4 < 1 := by linarith
  obtain ⟨s, hs, hcard, hmax, hinter⟩ :=
    rotationNeighborhood_exists_maximal_packing (positiveDiagonalFrame e he) (θ/4) hq0
  refine ⟨s, hs, ?_, hmax, ?_, ?_⟩
  · calc
      (s.card : ℝ) ≤ 1 / (rotationHaarMeasure
          (rotationNeighborhood (positiveDiagonalFrame e he) (θ/4))).toReal := hcard
      _ ≤ (C / (θ/4)^3) * (e 2 / e 0)^2 := hrec e he h01 h12 _ hq0 hqsmall
      _ = ((64*C) / θ^3) * (e 2 / e 0)^2 := by ring
  · intro O
    obtain ⟨P, hP, hOP⟩ := hinter O
    refine ⟨P, hP, ?_⟩
    have hrel := rotationNeighborhood_relative_of_translate_intersection
      (positiveDiagonalFrame e he) (θ/4) hq1 P O (fun h => hOP h.symm)
    apply rotationNeighborhood_mono (positiveDiagonalFrame e he) (show 2*(θ/4)/(1-θ/4) ≤ θ from ?_) hrel
    apply (div_le_iff₀ (by linarith : 0 < 1-θ/4)).mpr
    nlinarith [mul_lt_mul_of_pos_left hθ hθ0]
  · intro O hO P hP hne
    exact rotationNeighborhood_packing_separated (positiveDiagonalFrame e he) (θ/4) hq0
      s hs O P hO hP hne

end PaperI
