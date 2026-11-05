import PaperILean.PortfolioAtlasNorms
import PaperILean.ProjectedContinuedFrameCount

/-! Original indexed overlap for the stated continued normalization family.
Each nonempty frame fiber is anchored at an original label. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm
namespace PaperI.PortfolioAtlasOverlap

open Set ProjectedParallelogramArea ProjectedContinuedFrameCount
open ProjectedNormalizationRightFactors ExceptionalFiberPackingStage

/-- The original local-packing hypothesis bounds the number of covering labels,
including repetitions, after the normal-frame cardinality and right-factor
applications. No indexed overlap bound is a premise. -/
theorem indexed_overlap
    (G : MvPolynomial (Fin 3) ℝ) (D : ℕ) (hdegree : G.totalDegree ≤ D)
    (C P a Λ r : ℝ) (hP : 2 ≤ P) (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (n : ℕ) (N : Set (Fin 6 → ℝ))
    (g k : Fin n → Fin 6 → ℝ) (u : Fin n → (ℝ × ℝ) → Fin 6 → ℝ)
    (hcoords : ∀ i p, p ∈ square r → u i p 4 = p.1 ∧ u i p 5 = p.2)
    (hcontinue : ∀ i p, p ∈ square r →
      originalUpperAffineComp (originalUpperAffineComp (g i) (k i)) (u i p) ∈ N)
    (hbound : ∀ i p, p ∈ square r →
      ‖homogeneous (k i)‖ ≤ P ^ C ∧
      ‖homogeneous (originalUpperAffineInv (k i))‖ ≤ P ^ C ∧
      ‖homogeneous (u i p)‖ ≤ P ^ C ∧
      ‖homogeneous (originalUpperAffineInv (u i p))‖ ≤ P ^ C)
    (hpacking : ∀ i M, 2 ≤ M →
      ((Finset.univ.filter (fun j => relativeNeighborhoodRadius (g i) (g j) ≤ M)).card : ℝ) ≤
        Λ * M ^ a)
    (hnormal : ∀ v ∈ N,
      encode v ∈ NormalFibers.normalizedFrames G (v 4) (v 5)) :
    ∀ x : ℝ × ℝ,
      ((Finset.univ.filter (fun i =>
        x ∈ parallelogram ((originalUpperAffineComp (g i) (k i)) 4)
          ((originalUpperAffineComp (g i) (k i)) 5)
          ((originalUpperAffineComp (g i) (k i)) 3) r)).card : ℝ) ≤
        3 * (D : ℝ) * P ^ ((4 * max C 0 + 3) * a) * Λ := by
  classical
  intro x
  let h : Fin n → Fin 6 → ℝ := fun i => originalUpperAffineComp (g i) (k i)
  let Q : Fin n → Set (ℝ × ℝ) := fun i =>
    parallelogram (h i 4) (h i 5) (h i 3) r
  obtain ⟨hfinite, hcard, hwitness⟩ := projected_continued_frame_count_stage
    G D hdegree n N r h u hcoords hcontinue
    (fun v hv => by simpa only [NormalFibers.normalizedFrames, Set.mem_setOf_eq, encode]
      using hnormal v hv) x
  have hzero : (0, 0) ∈ square r := by simpa only [square, Set.mem_setOf_eq, abs_zero] using And.intro hr hr
  let p : Fin n → ℝ × ℝ := fun i =>
    if hi : x ∈ Q i then Classical.choose (hwitness i hi) else (0, 0)
  have hp (i : Fin n) : p i ∈ square r := by
    by_cases hi : x ∈ Q i
    · simpa only [p, dif_pos hi] using (Classical.choose_spec (hwitness i hi)).1
    · simpa only [p, dif_neg hi] using hzero
  let v : Fin n → Fin 6 → ℝ := fun i => u i (p i)
  let w : Fin n → Fin 6 → ℝ := fun i => originalUpperAffineComp (h i) (v i)
  let I : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ Q i)
  let S : Finset (Fin 6 → ℝ) := hfinite.toFinset
  have hw (i : Fin n) (hi : i ∈ I) : w i ∈ S := by
    have hcov : x ∈ Q i := (Finset.mem_filter.mp hi).2
    apply hfinite.mem_toFinset.mpr
    simpa only [w, v, p, dif_pos hcov] using (Classical.choose_spec (hwitness i hcov)).2
  let M : ℝ := P ^ (4 * max C 0 + 3)
  have hM : 2 ≤ M := PortfolioAtlasNorms.packing_radius_ge_two C P hP
  have hB : 0 ≤ Λ * M ^ a := mul_nonneg hΛ (Real.rpow_nonneg (by linarith : 0 ≤ M) a)
  have hfiber (z : Fin 6 → ℝ) :
      ((I.filter (fun i => w i = z)).card : ℝ) ≤ Λ * M ^ a := by
    by_cases hn : (I.filter (fun i => w i = z)).Nonempty
    · obtain ⟨i, hi⟩ := hn
      have hiw : w i = z := (Finset.mem_filter.mp hi).2
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hpacking i M hM)
      intro j hj
      have hjw : w j = z := (Finset.mem_filter.mp hj).2
      have hsame : originalUpperAffineComp
          (originalUpperAffineComp (g i) (k i)) (v i) =
          originalUpperAffineComp (originalUpperAffineComp (g j) (k j)) (v j) :=
        hiw.trans hjw.symm
      obtain ⟨_, hrelative, _, hf, hinv⟩ := projected_normalization_right_factors_stage
        C P hP n g k v (fun l => hbound l (p l) (hp l)) i j hsame
      have hf' : ‖homogeneous (originalUpperRelativeFrame (g i) (g j))‖ ≤ P ^ (4 * C) := by
        change ‖homogeneous (originalUpperAffineComp (originalUpperAffineInv (g i)) (g j))‖ ≤ _
        rwa [← hrelative]
      have hi' : ‖homogeneous
          (originalUpperAffineInv (originalUpperRelativeFrame (g i) (g j)))‖ ≤ P ^ (4 * C) := by
        change ‖homogeneous (originalUpperAffineInv
          (originalUpperAffineComp (originalUpperAffineInv (g i)) (g j)))‖ ≤ _
        rwa [← hrelative]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        PortfolioAtlasNorms.relative_radius_of_homogeneous_bounds C P hP (g i) (g j) hf' hi'⟩
    · have he : I.filter (fun i => w i = z) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simpa only [he, Finset.card_empty, Nat.cast_zero] using hB
  have hsum : I.card = ∑ z ∈ S, (I.filter (fun i => w i = z)).card :=
    Finset.card_eq_sum_card_fiberwise hw
  have hScard : S.card ≤ 3 * D := by
    simpa only [S, ← Set.ncard_eq_toFinset_card] using hcard
  have hI : (I.card : ℝ) ≤ (3 * D : ℕ) * (Λ * M ^ a) := by
    calc
      (I.card : ℝ) = ∑ z ∈ S, ((I.filter (fun i => w i = z)).card : ℝ) := by
        rw [hsum]
        norm_cast
      _ ≤ ∑ _z ∈ S, Λ * M ^ a := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (S.card : ℝ) * (Λ * M ^ a) := by simp
      _ ≤ (3 * D : ℕ) * (Λ * M ^ a) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hScard) hB
  change (I.card : ℝ) ≤ _
  apply hI.trans_eq
  dsimp [M]
  rw [← Real.rpow_mul (by linarith : 0 ≤ P)]
  push_cast
  ring

end PaperI.PortfolioAtlasOverlap
