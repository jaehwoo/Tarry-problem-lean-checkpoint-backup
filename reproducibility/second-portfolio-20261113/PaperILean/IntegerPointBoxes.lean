import PaperILean.MatrixCubeLabels
import Mathlib.Data.Set.Card

/-! I337: finite integer boxes with a bound uniform in their real centers.
The endpoint overhead is retained, including radius zero and empty point sets. -/
noncomputable section
open scoped BigOperators
namespace PaperI

def integerPhysicalVector (z : Fin 3 → ℤ) : PhysicalSpace := fun i => (z i : ℝ)

def integerIntervalAround (x r : ℝ) : Finset ℤ := Finset.Icc ⌊x - r⌋ ⌊x + r⌋

def integerPointBox (a : PhysicalSpace) (r : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun i => integerIntervalAround (a i) r

theorem mem_integerIntervalAround_of_abs_le (x r : ℝ) (z : ℤ)
    (h : |(z : ℝ) - x| ≤ r) : z ∈ integerIntervalAround x r := by
  have hz := abs_le.mp h
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.cast_le.mp (show (⌊x-r⌋ : ℝ) ≤ (z : ℝ) from
      (Int.floor_le (x-r)).trans (by linarith))
  · exact Int.le_floor.mpr (by linarith)

theorem integerIntervalAround_card_le (x r : ℝ) (hr : 0 ≤ r) :
    ((integerIntervalAround x r).card : ℝ) ≤ 2 * r + 2 := by
  have hlo : ⌊x-r⌋ ≤ ⌊x+r⌋ := Int.floor_mono (by linarith)
  have hc : ((integerIntervalAround x r).card : ℤ) = ⌊x+r⌋ + 1 - ⌊x-r⌋ :=
    Int.card_Icc_of_le (a := ⌊x-r⌋) (b := ⌊x+r⌋) (by omega)
  have hc' : ((integerIntervalAround x r).card : ℝ) =
      (⌊x+r⌋ : ℝ) + 1 - (⌊x-r⌋ : ℝ) := by exact_mod_cast hc
  rw [hc']
  have hu := Int.floor_le (x+r)
  have hl := Int.sub_one_lt_floor (x-r)
  linarith

theorem mem_integerPointBox_of_coordinate_bound (a : PhysicalSpace) (r : ℝ)
    (z : Fin 3 → ℤ) (h : ∀ i, |(z i : ℝ) - a i| ≤ r) :
    z ∈ integerPointBox a r := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact mem_integerIntervalAround_of_abs_le (a i) r (z i) (h i)

theorem integerPointBox_card_le (a : PhysicalSpace) (r : ℝ) (hr : 0 ≤ r) :
    ((integerPointBox a r).card : ℝ) ≤ (2*r+2)^3 := by
  have hc : (integerPointBox a r).card = ∏ i : Fin 3, (integerIntervalAround (a i) r).card :=
    Fintype.card_piFinset _
  rw [hc, Nat.cast_prod]
  calc
    (∏ i : Fin 3, ((integerIntervalAround (a i) r).card : ℝ)) ≤
        ∏ _i : Fin 3, (2*r+2) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => integerIntervalAround_card_le (a i) r hr)
    _ = (2*r+2)^3 := by simp

theorem integerPointSet_finite_of_coordinate_bound (Z : Set (Fin 3 → ℤ))
    (a : PhysicalSpace) (r : ℝ)
    (hZ : ∀ z ∈ Z, ∀ i, |(z i : ℝ) - a i| ≤ r) : Z.Finite := by
  exact (integerPointBox a r).finite_toSet.subset
    (fun z hz => mem_integerPointBox_of_coordinate_bound a r z (hZ z hz))

theorem integerPointSet_ncard_le (Z : Set (Fin 3 → ℤ))
    (a : PhysicalSpace) (r : ℝ) (hr : 0 ≤ r)
    (hZ : ∀ z ∈ Z, ∀ i, |(z i : ℝ) - a i| ≤ r) :
    (Z.ncard : ℝ) ≤ (2*r+2)^3 := by
  have hs : Z ⊆ (↑(integerPointBox a r) : Set (Fin 3 → ℤ)) :=
    fun z hz => mem_integerPointBox_of_coordinate_bound a r z (hZ z hz)
  have hc : Z.ncard ≤ (integerPointBox a r).card := by
    simpa using Set.ncard_le_ncard hs (integerPointBox a r).finite_toSet
  exact (Nat.cast_le.mpr hc).trans (integerPointBox_card_le a r hr)

end PaperI
