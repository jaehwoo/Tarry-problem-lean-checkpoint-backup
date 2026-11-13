import PaperILean.PublishedFormatAnalyticCuts
import PaperILean.PreparationIntervalSelection
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! I1263: select an actual long regular interval of the supplied centerline.
The cut bound precedes every coefficient, function and endpoint. No extension
of the function outside the represented closed interval is assumed regular. -/

noncomputable section
namespace PaperI
open Set
open scoped BigOperators

theorem exists_long_consecutive_cut_interval (C : Finset ℝ) {a b : ℝ}
    (hab : a < b) (ha : a ∈ C) (hb : b ∈ C)
    (hC : ∀ c ∈ C, c ∈ Icc a b) {K : ℕ} (hcard : C.card ≤ K) :
    ∃ u ∈ C, ∃ v ∈ C, u < v ∧
      (b-a) / ((K : ℝ)+1) ≤ v-u ∧ ∀ c ∈ C, c ∉ Ioo u v := by
  obtain ⟨n,t,hn,ht0,htn,_,hgap⟩ := exists_sorted_cut_partition C ha hb hC
  have hsum : b-a ≤ ∑ j ∈ Finset.range n, (t (j+1)-t j) := by
    rw [Finset.sum_range_sub, ht0, htn]
  obtain ⟨j,hj,hlen⟩ := preparation_exists_large_member (Finset.range n)
    (fun j => t (j+1)-t j) (sub_pos.mpr hab) (Nat.succ_pos K)
    (by rw [Finset.card_range]; omega) hsum
  obtain ⟨hu,hv,huv,hno⟩ := hgap j (Finset.mem_range.mp hj)
  exact ⟨t j,hu,t (j+1),hv,huv,by simpa only [Nat.cast_succ] using hlen,hno⟩

theorem published_bounded_format_long_analytic_interval
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPiece : PublishedPiecewiseNashExtensions) (s D : ℕ) :
    ∃ K : ℕ, 0 < K ∧
      ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Icc a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x) →
      ∃ u v : ℝ, a ≤ u ∧ u < v ∧ v ≤ b ∧ (b-a)/(K : ℝ) ≤ v-u ∧
        AnalyticOnNhd ℝ f (Ioo u v) := by
  obtain ⟨K,hK⟩ := published_bounded_sign_format_analytic_cut_sets
    hCell hHardt hQE hPiece s D
  refine ⟨K+1,Nat.succ_pos K,?_⟩
  intro A S hc hd hS f a b hab hrep
  obtain ⟨C,ha,hb,hC,hA,hcard⟩ := hK A S hc hd hS f a b hab.le hrep
  obtain ⟨u,hu,v,hv,huv,hlen,hgap⟩ := exists_long_consecutive_cut_interval
    C hab ha hb hC hcard
  exact ⟨u,v,(hC u hu).1,huv,(hC v hv).2,
    by simpa only [Nat.cast_add,Nat.cast_one] using hlen,hA u hu v hv huv hgap⟩

end PaperI
