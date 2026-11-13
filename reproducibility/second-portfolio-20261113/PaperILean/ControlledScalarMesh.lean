import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! I1261: an on-curve finite mesh controlled by a continuous monotone scalar.
The final index is included even at integral mesh ratios. Constant curves and
degenerate parameter intervals are allowed. This is a coordinate-variation
mesh, not a claim to construct Euclidean arclength parametrization. -/

noncomputable section
namespace PaperI
open Set

theorem controlled_scalar_finite_mesh {X : Type*} [PseudoMetricSpace X]
    (γ : ℝ → X) (f : ℝ → ℝ) {a b W : ℝ} (hab : a ≤ b) (hW : 0 < W)
    (hc : ContinuousOn f (Icc a b)) (hm : MonotoneOn f (Icc a b))
    (hd : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (γ s) (γ t) ≤ |f s-f t|) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : Fin n → ℝ,
      (∀ i, times i ∈ Icc a b) ∧
      (n : ℝ)*W ≤ f b-f a+W ∧
      ∀ t ∈ Icc a b, ∃ i, dist (γ t) (γ (times i)) < W := by
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have hV : 0 ≤ f b-f a := sub_nonneg.mpr (hm ha hb hab)
  let N : ℕ := ⌊(f b-f a)/W⌋₊
  have hN : (N : ℝ)*W ≤ f b-f a :=
    (le_div_iff₀ hW).mp (Nat.floor_le (div_nonneg hV hW.le))
  have hlevel (i : Fin (N+1)) : f a+(i.val : ℝ)*W ∈ Icc (f a) (f b) := by
    have hi : (i.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hW.le)
    · linarith [mul_le_mul_of_nonneg_right hi hW.le]
  have htime (i : Fin (N+1)) : ∃ t ∈ Icc a b, f t=f a+(i.val : ℝ)*W :=
    intermediate_value_Icc hab hc (hlevel i)
  choose times ht he using htime
  refine ⟨N+1,Nat.succ_pos _,times,ht,?_,?_⟩
  · push_cast
    nlinarith
  · intro t hti
    have hta : 0 ≤ f t-f a := sub_nonneg.mpr (hm ha hti hti.1)
    have htb : f t-f a ≤ f b-f a := sub_le_sub_right (hm hti hb hti.2) _
    let k : ℕ := ⌊(f t-f a)/W⌋₊
    have hkN : k ≤ N := Nat.floor_le_floor (div_le_div_of_nonneg_right htb hW.le)
    let i : Fin (N+1) := ⟨k,Nat.lt_succ_of_le hkN⟩
    have hk : (k : ℝ)*W ≤ f t-f a :=
      (le_div_iff₀ hW).mp (Nat.floor_le (div_nonneg hta hW.le))
    have hk' : f t-f a < ((k : ℝ)+1)*W :=
      (div_lt_iff₀ hW).mp (Nat.lt_floor_add_one ((f t-f a)/W))
    refine ⟨i,(hd t hti (times i) (ht i)).trans_lt ?_⟩
    rw [he i]
    change |f t-(f a+(k : ℝ)*W)| < W
    rw [abs_of_nonneg (by linarith)]
    nlinarith

end PaperI
