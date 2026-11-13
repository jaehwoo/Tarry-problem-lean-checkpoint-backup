import PaperILean.EuclideanArclengthClock

/-! I1261: select equally spaced attained levels of the actual Euclidean
arclength clock. No inverse-clock regularity or nonzero length is assumed. -/

noncomputable section
namespace PaperI
open Set

theorem continuous_monotone_equal_spacing_mesh (f : ℝ → ℝ) {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn f (Icc a b))
    (hm : MonotoneOn f (Icc a b)) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : Fin n → ℝ,
      (∀ i, times i ∈ Icc a b) ∧ StrictMono times ∧
      (∀ i, f (times i) = f a + (i.val : ℝ)*W) ∧
      (n : ℝ)*W ≤ f b-f a+W ∧
      ∀ t ∈ Icc a b, ∃ i, 0 ≤ f t-f (times i) ∧ f t-f (times i) < W := by
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have hV : 0 ≤ f b-f a := sub_nonneg.mpr (hm ha hb hab)
  let N : ℕ := ⌊(f b-f a)/W⌋₊
  have hN : (N : ℝ)*W ≤ f b-f a :=
    (le_div_iff₀ hW).mp (Nat.floor_le (div_nonneg hV hW.le))
  have hlevel (i : Fin (N+1)) : f a+(i.val : ℝ)*W ∈ Icc (f a) (f b) := by
    have hi : (i.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hW.le),
      by linarith [mul_le_mul_of_nonneg_right hi hW.le]⟩
  have htime (i : Fin (N+1)) : ∃ t ∈ Icc a b, f t=f a+(i.val : ℝ)*W :=
    intermediate_value_Icc hab hc (hlevel i)
  choose times ht he using htime
  refine ⟨N+1,Nat.succ_pos _,times,ht,?_,he,?_,?_⟩
  · intro i j hij
    by_contra hn
    have h := hm (ht j) (ht i) (le_of_not_gt hn)
    rw [he i,he j] at h
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    nlinarith
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
    refine ⟨i,?_,?_⟩ <;> rw [he i] <;> dsimp only [i] <;> linarith

theorem monotone_planar_arc_arclength_mesh {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hW : 0 < W) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b)) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : Fin n → ℝ,
      (∀ i, times i ∈ Icc a b) ∧ StrictMono times ∧
      (∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W) ∧
      (n : ℝ)*W ≤ planarEuclideanLength γ a b+W ∧
      ∀ t ∈ Icc a b, ∃ i,
        |planarEuclideanLength γ a t-planarEuclideanLength γ a (times i)| < W ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ t))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times i))) < W := by
  obtain ⟨n,hn,times,ht,hmono,he,hcount,hmesh⟩ :=
    continuous_monotone_equal_spacing_mesh (planarEuclideanLength γ a) hab hW
      (planar_arclength_clock_continuous hc hm) (planar_arclength_clock_monotone hm)
  refine ⟨n,hn,times,ht,hmono,?_,?_,?_⟩
  · simpa only [planar_euclidean_length_self,zero_add] using he
  · simpa only [planar_euclidean_length_self,sub_zero] using hcount
  · intro t hti
    obtain ⟨i,hi,hi'⟩ := hmesh t hti
    have hlt : |planarEuclideanLength γ a t-planarEuclideanLength γ a (times i)| < W := by
      rwa [abs_of_nonneg hi]
    exact ⟨i,hlt,(planar_dist_le_arclength_clock hm t hti (times i) (ht i)).trans_lt hlt⟩

theorem arclength_mesh_subarc_length {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ} {n : ℕ}
    (hm : ∀ i, MonotoneOn (fun t => γ t i) (Icc a b) ∨
      AntitoneOn (fun t => γ t i) (Icc a b))
    (times : Fin n → ℝ) (ht : ∀ i, times i ∈ Icc a b) (hmono : Monotone times)
    (he : ∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W)
    {i j : Fin n} (hij : i ≤ j) :
    planarEuclideanLength γ (times i) (times j) = ((j.val : ℝ)-i.val)*W := by
  rw [← planar_arclength_clock_increment hm (ht i) (ht j) (hmono hij),he i,he j]
  ring

theorem arclength_mesh_zero_length_count {L W : ℝ} {n : ℕ}
    (hn : 0 < n) (hW : 0 < W) (hz : L = 0) (hcount : (n : ℝ)*W ≤ L+W) :
    n = 1 := by
  have hn' : (n : ℝ) ≤ 1 := by rw [hz,zero_add] at hcount; nlinarith
  have hn'' : n ≤ 1 := by exact_mod_cast hn'
  omega

end PaperI
