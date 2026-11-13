import PaperILean.UniformPlanarGraphPartitions
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! I1263: finite polygon inequality and a maximal longitudinal span select
one graph piece of macroscopic projection length. No lower width, nonzero
speed, simple-path or injective-parameter assumption is used. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem planar_euclidean_dist_le_coordinate_sum (x y : Fin 2 → ℝ) :
    dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x)
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm y) ≤ |x 0-y 0|+|x 1-y 1| := by
  rw [PiLp.dist_eq_of_L2,Fin.sum_univ_two]
  simp only [WithLp.equiv_symm_pi_apply,Real.dist_eq]
  rw [Real.sqrt_le_left (add_nonneg (abs_nonneg _) (abs_nonneg _))]
  nlinarith [mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

/-- Graph data with an explicit lower span estimate, in the same chosen
coordinate and orientation as the graph. The range interval may be a point. -/
def SpanningPlanarGraphArc (γ : ℝ → Fin 2 → ℝ) (a b R C : ℝ) : Prop :=
  ∃ i k : Fin 2, i ≠ k ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
    MonotoneOn (fun t => σ*γ t i) (Icc a b) ∧
    R ≤ C*(σ*γ b i-σ*γ a i) ∧
    ∃ h : ℝ → ℝ, LipschitzOnWith 1 h (Icc (σ*γ a i) (σ*γ b i)) ∧
      (∀ t ∈ Icc a b, h (σ*γ t i)=γ t k) ∧
      ∀ q ∈ Icc (σ*γ a i) (σ*γ b i), ∃ t ∈ Icc a b, σ*γ t i=q

theorem exists_macroscopic_planar_graph_piece
    (γ : ℝ → Fin 2 → ℝ) (n : ℕ) (t : ℕ → ℝ) (hn : 0 < n)
    (ht : ∀ j < n, t j ≤ t (j+1))
    (harc : ∀ j < n, SignedPlanarGraphArc γ (t j) (t (j+1))) :
    ∃ j < n, SpanningPlanarGraphArc γ (t j) (t (j+1))
      (dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (t 0)))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (γ (t n)))) (2*(n : ℝ)) := by
  classical
  have ha (j : Fin n) : SignedPlanarGraphArc γ (t j.val) (t (j.val+1)) := harc j.val j.isLt
  choose i k hik σ hσ hm hdom h hLip hEq hOnto using ha
  let L : Fin n → ℝ := fun j => |γ (t (j.val+1)) (i j)-γ (t j.val) (i j)|
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) L
    ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hend (c : Fin 2) : |γ (t 0) c-γ (t n) c| ≤ (n : ℝ)*L j := by
    have hb : ∀ {r : ℕ}, r < n →
        dist (γ (t r) c) (γ (t (r+1)) c) ≤ L j := by
      intro r hr
      have hu : t r ∈ Icc (t r) (t (r+1)) := ⟨le_rfl,ht r hr⟩
      have hv : t (r+1) ∈ Icc (t r) (t (r+1)) := ⟨ht r hr,le_rfl⟩
      have hd := hdom ⟨r,hr⟩ (t r) hu (t (r+1)) hv c
      have hd' : dist (γ (t r) c) (γ (t (r+1)) c) ≤ L ⟨r,hr⟩ := by
        simpa only [Real.dist_eq,L,abs_sub_comm] using hd
      exact hd'.trans (hmax ⟨r,hr⟩ (Finset.mem_univ _))
    simpa only [Real.dist_eq,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
      dist_le_range_sum_of_dist_le (f := fun r => γ (t r) c) n hb
  have hdist := planar_euclidean_dist_le_coordinate_sum (γ (t 0)) (γ (t n))
  have hwidth : σ j*γ (t (j.val+1)) (i j)-σ j*γ (t j.val) (i j)=L j := by
    have hw := hm j ⟨le_rfl,ht j.val j.isLt⟩ ⟨ht j.val j.isLt,le_rfl⟩ (ht j.val j.isLt)
    have hnon : 0 ≤ σ j*γ (t (j.val+1)) (i j)-σ j*γ (t j.val) (i j) := sub_nonneg.mpr hw
    rw [← abs_of_nonneg hnon]
    rcases hσ j with hs | hs
    · simp only [hs,one_mul,L]
    · simp only [hs,neg_one_mul,neg_sub_neg,L,abs_sub_comm]
  refine ⟨j.val,j.isLt,i j,k j,hik j,σ j,hσ j,hm j,?_,h j,hLip j,hEq j,hOnto j⟩
  rw [hwidth]
  linarith [hend 0,hend 1]

theorem spanningPlanarGraphArc_mono_scale {γ : ℝ → Fin 2 → ℝ} {a b R C D : ℝ}
    (hab : a ≤ b) (hCD : C ≤ D) (h : SpanningPlanarGraphArc γ a b R C) :
    SpanningPlanarGraphArc γ a b R D := by
  obtain ⟨i,k,hik,σ,hσ,hm,hbound,f,hLip,hEq,hOnto⟩ := h
  have hn : 0 ≤ σ*γ b i-σ*γ a i :=
    sub_nonneg.mpr (hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)
  exact ⟨i,k,hik,σ,hσ,hm,hbound.trans (mul_le_mul_of_nonneg_right hCD hn),f,hLip,hEq,hOnto⟩

theorem spanningPlanarGraphArc_positive_span {γ : ℝ → Fin 2 → ℝ} {a b R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (h : SpanningPlanarGraphArc γ a b R C) :
    ∃ i : Fin 2, 0 < |γ b i-γ a i| := by
  obtain ⟨i,k,hik,σ,hσ,hm,hbound,hRest⟩ := h
  have hw : 0 < σ*γ b i-σ*γ a i := by
    by_contra hnot
    have := mul_nonpos_of_nonneg_of_nonpos hC (le_of_not_gt hnot)
    linarith
  refine ⟨i,abs_pos.mpr ?_⟩
  intro he
  have hx := sub_eq_zero.mp he
  rw [hx,sub_self] at hw
  exact (lt_irrefl 0) hw

end PaperI
