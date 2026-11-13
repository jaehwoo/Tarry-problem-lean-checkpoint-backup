import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import PaperILean.FiniteConnectedCover

/-! Open interval components and exceptional-length bookkeeping for I950.
This module makes no quantitative semialgebraic or derivative-bound assertion. -/

noncomputable section
namespace PaperI
open Set MeasureTheory
open scoped ENNReal

/-- A nonempty, bounded, open connected real set is its endpoint interval. -/
theorem bounded_open_connected_eq_Ioo {V : Set ℝ} (ho : IsOpen V)
    (hc : IsConnected V) (hl : BddBelow V) (hu : BddAbove V) :
    V = Ioo (sInf V) (sSup V) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨p, q, hpq, hpqV⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hx)
    obtain ⟨y, hpy, hyx⟩ := exists_between hpq.1
    obtain ⟨z, hxz, hzq⟩ := exists_between hpq.2
    exact ⟨csInf_lt_of_lt hl (hpqV ⟨hpy, hyx.trans hpq.2⟩) hyx,
      lt_csSup_of_lt hu (hpqV ⟨hpq.1.trans hxz, hzq⟩) hxz⟩
  · exact hc.Ioo_csInf_csSup_subset hl hu

/-- Each component of an open subset of a bounded real interval is an open
interval. The family is indexed by the actual component quotient, including
the empty index type when `U` is empty. -/
theorem open_set_component_intervals {U : Set ℝ} {a b : ℝ}
    (ho : IsOpen U) (hsub : U ⊆ Ioo a b) :
    ∃ l r : ConnectedComponents U → ℝ,
      (∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ Ioo (l i) (r i) ⊆ U) ∧
      U = ⋃ i, Ioo (l i) (r i) := by
  classical
  let rep : ConnectedComponents U → U := fun i =>
    (ConnectedComponents.surjective_coe i).choose
  have hrep (i : ConnectedComponents U) : ConnectedComponents.mk (rep i) = i :=
    (ConnectedComponents.surjective_coe i).choose_spec
  let C : ConnectedComponents U → Set ℝ := fun i => connectedComponentIn U (rep i).val
  have hCsub (i) : C i ⊆ U := connectedComponentIn_subset _ _
  have hCconn (i) : IsConnected (C i) :=
    isConnected_connectedComponentIn_iff.mpr (rep i).property
  have hCl (i) : BddBelow (C i) := ⟨a, fun x hx => (hsub (hCsub i hx)).1.le⟩
  have hCu (i) : BddAbove (C i) := ⟨b, fun x hx => (hsub (hCsub i hx)).2.le⟩
  have hCo (i) : IsOpen (C i) := ho.connectedComponentIn
  have hCeq (i) : C i = Ioo (sInf (C i)) (sSup (C i)) :=
    bounded_open_connected_eq_Ioo (hCo i) (hCconn i) (hCl i) (hCu i)
  refine ⟨fun i => sInf (C i), fun i => sSup (C i), ?_, ?_⟩
  · intro i
    refine ⟨le_csInf (hCconn i).nonempty (fun x hx => (hsub (hCsub i hx)).1.le), ?_,
      csSup_le (hCconn i).nonempty (fun x hx => (hsub (hCsub i hx)).2.le), ?_⟩
    · exact Set.nonempty_Ioo.mp ((hCeq i) ▸ (hCconn i).nonempty)
    · rw [← hCeq i]
      exact hCsub i
  · apply Set.Subset.antisymm
    · intro x hx
      let xx : U := ⟨x, hx⟩
      let i : ConnectedComponents U := ConnectedComponents.mk xx
      have heq : ConnectedComponents.mk xx = ConnectedComponents.mk (rep i) :=
        (hrep i).symm
      have hxc : x ∈ C i := by
        rw [show C i = connectedComponentIn U (rep i).val from rfl,
          connectedComponentIn_eq_image (rep i).property]
        exact ⟨xx, ConnectedComponents.coe_eq_coe'.mp heq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, (hCeq i) ▸ hxc⟩
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hCsub i ((hCeq i).symm ▸ hi)

/-- A uniform bound on the lengths of contained open subintervals, together
with a bound on the finite component quotient, controls the exceptional length.
No positivity assumption on `c` is needed for this extended-real formulation. -/
theorem volume_open_set_le_component_count_mul {U : Set ℝ} {a b c : ℝ} {K : ℕ}
    (ho : IsOpen U) (hsub : U ⊆ Ioo a b)
    [Finite (ConnectedComponents U)] (hK : Nat.card (ConnectedComponents U) ≤ K)
    (hlen : ∀ u v : ℝ, a ≤ u → u < v → v ≤ b → Ioo u v ⊆ U → v - u ≤ c) :
    volume U ≤ (K : ℝ≥0∞) * ENNReal.ofReal c := by
  classical
  letI := Fintype.ofFinite (ConnectedComponents U)
  obtain ⟨l, r, hparts, hcover⟩ := open_set_component_intervals ho hsub
  calc
    volume U = volume (⋃ i, Ioo (l i) (r i)) := congrArg volume hcover
    _ ≤ ∑ i, volume (Ioo (l i) (r i)) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _i : ConnectedComponents U, ENNReal.ofReal c := by
      apply Finset.sum_le_sum
      intro i _
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_le_ofReal
        (hlen (l i) (r i) (hparts i).1 (hparts i).2.1 (hparts i).2.2.1 (hparts i).2.2.2)
    _ = (Nat.card (ConnectedComponents U) : ℝ≥0∞) * ENNReal.ofReal c := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (K : ℝ≥0∞) * ENNReal.ofReal c := by
      exact mul_le_mul_right' (by exact_mod_cast hK) _

end PaperI
