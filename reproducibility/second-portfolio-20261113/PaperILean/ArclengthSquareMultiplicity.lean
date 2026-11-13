import PaperILean.PlanarMeshSquares

/-! The arclength square cover has bounded pointwise multiplicity on a
coordinate-monotone arc. Arclength separation alone would not suffice for
arbitrary curves that repeatedly return to the same location. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable

theorem finite_index_card_le_of_span {n K : ℕ} (S : Finset (Fin n))
    (hspan : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → j.val ≤ i.val+K) :
    S.card ≤ K+1 := by
  classical
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    have hi : i ∈ S := Finset.min'_mem S hS
    have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.Icc i.val (i.val+K))
      Fin.val (fun j hj => Finset.mem_Icc.mpr
        ⟨Finset.min'_le S j hj,hspan i hi j hj (Finset.min'_le S j hj)⟩)
      (fun _ _ _ _ h => Fin.ext h)
    simp only [Nat.card_Icc] at h
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty,Nat.zero_le]

theorem arclength_mesh_nearby_index_span {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ} {n : ℕ}
    (hW : 0 < W)
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (times : Fin n → ℝ) (ht : ∀ i, times i ∈ Icc a b) (hmono : Monotone times)
    (he : ∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W)
    (x : Fin 2 → ℝ) {i j : Fin n} (hij : i ≤ j)
    (hi : ∀ k, |γ (times i) k-x k| ≤ 5*W)
    (hj : ∀ k, |γ (times j) k-x k| ≤ 5*W) :
    j.val ≤ i.val+20 := by
  have hk (k : Fin 2) : |γ (times j) k-γ (times i) k| ≤ 10*W := by
    have := abs_sub_le (γ (times j) k) (x k) (γ (times i) k)
    rw [abs_sub_comm (x k)] at this
    linarith [hi k,hj k]
  have hlen := planar_euclidean_length_le_coordinate_variation (hmono hij)
    (planar_coordinate_monotone_restrict hm (ht i) (ht j))
  rw [arclength_mesh_subarc_length hm times ht hmono he hij] at hlen
  have hcast : (j.val : ℝ) ≤ (i.val : ℝ)+20 := by nlinarith [hk 0,hk 1]
  exact_mod_cast hcast

theorem arclength_mesh_nearby_index_count {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ} {n : ℕ}
    (hW : 0 < W)
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (times : Fin n → ℝ) (ht : ∀ i, times i ∈ Icc a b) (hmono : Monotone times)
    (he : ∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W)
    (x : Fin 2 → ℝ) :
    (Finset.univ.filter (fun i => ∀ k, |γ (times i) k-x k| ≤ 5*W)).card ≤ 21 := by
  classical
  apply finite_index_card_le_of_span (K := 20)
  intro i hi j hj hij
  exact arclength_mesh_nearby_index_span hW hm times ht hmono he x hij
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem arclength_square_cover_multiplicity {γ : ℝ → Fin 2 → ℝ} {a b W : ℝ} {n : ℕ}
    (hW : 0 < W)
    (hm : ∀ k, MonotoneOn (fun t => γ t k) (Icc a b) ∨
      AntitoneOn (fun t => γ t k) (Icc a b))
    (times : Fin n → ℝ) (ht : ∀ i, times i ∈ Icc a b) (hmono : Monotone times)
    (he : ∀ i, planarEuclideanLength γ a (times i) = (i.val : ℝ)*W)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (Finset.univ.filter (fun ik : Fin n × (Fin 2 → Fin 10) =>
      x ∈ planarSquare (planarMeshSquareCorner
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times ik.1))) W ik.2) W)).card ≤ 2100 := by
  classical
  let S := Finset.univ.filter (fun i => ∀ k, |γ (times i) k-x k| ≤ 5*W)
  have hsub : (Finset.univ.filter (fun ik : Fin n × (Fin 2 → Fin 10) =>
      x ∈ planarSquare (planarMeshSquareCorner
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (times ik.1))) W ik.2) W)) ⊆
      S ×ˢ (Finset.univ : Finset (Fin 2 → Fin 10)) := by
    intro ik hik
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,Finset.mem_univ _⟩
    have h := planar_mesh_square_coordinate_bounds _ x hW.le ik.2 (Finset.mem_filter.mp hik).2
    simpa only [WithLp.equiv_symm_pi_apply,abs_sub_comm] using h
  have hc : S.card ≤ 21 := arclength_mesh_nearby_index_count hW hm times ht hmono he x
  have h := Finset.card_le_card hsub
  simp only [Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_fin] at h
  omega

end PaperI
