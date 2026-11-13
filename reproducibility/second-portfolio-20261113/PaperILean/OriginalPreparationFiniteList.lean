import PaperILean.OriginalOneVariablePreparation
import PaperILean.OriginalPreparationSuperlevels
import PaperILean.PreparationIntervalSelection

/-! Original one-variable preparation for a finite scalar list. One constant is
chosen before every function, amplitude and interval. The construction uses the
proved divided-difference superlevel estimate, not an assumed good-set theorem.
The empty list, N=0, zero amplitude and arbitrary positive epsilon are retained. -/

noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped BigOperators ENNReal

/-- A fixed uniform signed-component bound yields the common measurable good
set. The count hypothesis is a prerequisite about actual superlevel sets, not
an assumption of the derivative estimate being proved. -/
theorem published_finite_list_preparation_of_component_bound
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    {ι : Type*} [Fintype ι] (N K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ι → ℝ → ℝ) (B : ι → ℝ) (a b : ℝ),
      a < b → (∀ i, 0 ≤ B i) →
      (∀ i, ContDiffOn ℝ N (f i) (Ioo a b)) →
      (∀ i, ∀ x ∈ Ioo a b, |f i x| ≤ B i) →
      (∀ i, ∀ n ≤ N, ∀ threshold sign : ℝ, |sign| = 1 →
        Finite (ConnectedComponents (signedIteratedDerivativeSuperlevel (f i) n a b threshold sign)) ∧
        Nat.card (ConnectedComponents (signedIteratedDerivativeSuperlevel (f i) n a b threshold sign)) ≤ K) →
      ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ioo a b ∧
        volume (Ioo a b \ G) ≤ ENNReal.ofReal (ε * (b-a)) ∧
        ∀ x ∈ G, ∀ i, ∀ n ≤ N, |iteratedDeriv n (f i) x| ≤ C * B i / (b-a)^n := by
  classical
  let den : ℝ := 2 * ((K : ℝ)+1) * ((N : ℝ)+1) * ((Fintype.card ι : ℝ)+1)
  have hden : 0 < den := by dsimp [den]; positivity
  let δ : ℝ := ε / den
  have hδ : 0 < δ := div_pos hε hden
  let c : Fin (N+1) → ℝ := fun j => (4 * (j.val : ℝ) / δ)^j.val
  have hc : ∀ j, 0 ≤ c j := by intro j; dsimp [c]; positivity
  let C : ℝ := 1 + ∑ j, c j
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hc j)
  have hCj : ∀ j : Fin (N+1), (4 * (j.val : ℝ) / δ)^j.val ≤ C := by
    intro j
    have hj := Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ j)
    change c j ≤ C
    dsimp [C]
    linarith
  refine ⟨C,hC1,?_⟩
  intro f B a b hab hB hsmooth hamp hcount
  have hL : 0 < b-a := sub_pos.mpr hab
  let E : ι × Fin (N+1) → Set ℝ := fun k =>
    {x | x ∈ Ioo a b ∧ C * B k.1 / (b-a)^k.2.val < |iteratedDeriv k.2.val (f k.1) x|}
  let budget : ℝ := 2 * (K : ℝ) * δ * (b-a)
  have hbudget : 0 ≤ budget := by dsimp [budget]; positivity
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    exact ((continuousOn_iteratedDeriv_of_contDiffOn_Ioo (hsmooth k.1)
      (Nat.lt_succ_iff.mp k.2.isLt)).abs.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi).measurableSet
  have hE : ∀ k, volume (E k) ≤ ENNReal.ofReal budget := by
    intro k
    by_cases hk : k.2.val = 0
    · have he : E k = ∅ := by
        ext x
        simp only [E, hk, iteratedDeriv_zero, pow_zero, div_one, mem_setOf_eq,
          mem_empty_iff_false, iff_false]
        rintro ⟨hx,hbad⟩
        have hm := hamp k.1 x hx
        have hmul : B k.1 ≤ C * B k.1 := by nlinarith [hB k.1]
        exact (not_lt_of_ge (hm.trans hmul)) hbad
      rw [he, measure_empty]
      exact bot_le
    · exact published_abs_derivative_superlevel_volume_le hDD k.2.val N K (f k.1)
        a b (B k.1) δ C (Nat.pos_of_ne_zero hk) (Nat.lt_succ_iff.mp k.2.isLt)
        hab (hB k.1) hδ (hCj k.2) (hsmooth k.1) (hamp k.1)
        (fun sign hsign => hcount k.1 k.2.val (Nat.lt_succ_iff.mp k.2.isLt) _ sign hsign)
  obtain ⟨G,hGm,hGsub,hGbad,hGood⟩ := preparation_common_measurable_good_set
    volume (Ioo a b) measurableSet_Ioo Finset.univ E (fun k _ => hEm k)
    (fun k x => |iteratedDeriv k.2.val (f k.1) x| ≤ C * B k.1 / (b-a)^k.2.val)
    (fun _ => budget) (fun _ _ => hbudget) (fun k _ => hE k)
    (fun k _ x hx hnot => le_of_not_gt (fun hlt => hnot ⟨hx,hlt⟩))
  have hcoef : 2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ) ≤ den := by
    dsimp [den]
    gcongr <;> linarith
  have hscaled : (2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ)) * δ ≤ ε := by
    calc
      _ ≤ den * δ := mul_le_mul_of_nonneg_right hcoef hδ.le
      _ = ε := by dsimp [δ]; field_simp [ne_of_gt hden]
  have htotal : (∑ _k : ι × Fin (N+1), budget) ≤ ε * (b-a) := by
    calc
      _ = (2 * (K : ℝ) * ((N : ℝ)+1) * (Fintype.card ι : ℝ)) * δ * (b-a) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, budget]
        ring
      _ ≤ ε * (b-a) := mul_le_mul_of_nonneg_right hscaled (sub_nonneg.mpr hab.le)
  refine ⟨G,hGm,hGsub,hGbad.trans (ENNReal.ofReal_le_ofReal htotal),?_⟩
  intro x hx i n hn
  exact hGood x hx (i,⟨n,Nat.lt_succ_iff.mpr hn⟩) (Finset.mem_univ _)

/-- The component prerequisite is supplied from bounded semialgebraic graph
format, uniformly over the whole list and all orders up to N. -/
theorem published_bounded_format_finite_list_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type*} [Fintype ι] (s D N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (A : ι → Finset (MvPolynomial (Fin 2) ℝ)) (S : ι → Set (Fin 2 → ℝ)),
      (∀ i, (A i).card ≤ s) → (∀ i, ∀ P ∈ A i, P.totalDegree ≤ D) →
      (∀ i, PolynomialSignDetermined (A i) (S i)) →
      ∀ (f : ι → ℝ → ℝ) (B : ι → ℝ) (a b : ℝ), a < b →
      (∀ i, ∀ t ∈ Ioo a b, ∀ y : ℝ, ![t,y] ∈ S i ↔ y = f i t) →
      (∀ i, ContDiffOn ℝ N (f i) (Ioo a b)) →
      (∀ i, ∀ x ∈ Ioo a b, |f i x| ≤ B i) →
      ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ioo a b ∧
        volume (Ioo a b \ G) ≤ ENNReal.ofReal (ε * (b-a)) ∧
        ∀ x ∈ G, ∀ i, ∀ n ≤ N, |iteratedDeriv n (f i) x| ≤ C * B i / (b-a)^n := by
  obtain ⟨K,hK⟩ := published_bounded_sign_format_iteratedDerivative_superlevel_components
    hCell hHardt hQE s D N
  obtain ⟨C,hC,hprep⟩ := published_finite_list_preparation_of_component_bound
    (ι := ι) hDD N K ε hε
  refine ⟨C,hC,?_⟩
  intro A S hcard hdeg hS f B a b hab hrep hsmooth hamp
  have hmid : (a+b)/2 ∈ Ioo a b := by constructor <;> linarith
  have hB : ∀ i, 0 ≤ B i := fun i => (abs_nonneg _).trans (hamp i _ hmid)
  exact hprep f B a b hab hB hsmooth hamp (fun i n hn threshold sign _ =>
    hK (A i) (S i) (hcard i) (hdeg i) (hS i) (f i) a b threshold sign
      (hrep i) (hsmooth i) n hn)

end PaperI
