import PaperILean.AttainedMaximumDefinability
import PaperILean.CompactFamilyMaximum

/-! I625-638: a first-order formula for the exact attained maximum.
This is formula closure, not real quantifier elimination. -/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def familyValueGraph {ι : Type*} (K : ℝ → Set (ι → ℝ))
    (g : ℝ → (ι → ℝ) → ℝ) : Set (((Unit ⊕ ι) ⊕ Unit) → ℝ) :=
  {v | 2 ≤ v (Sum.inl (Sum.inl ())) ∧
    (fun i => v (Sum.inl (Sum.inr i))) ∈ K (v (Sum.inl (Sum.inl ()))) ∧
    v (Sum.inr ()) = g (v (Sum.inl (Sum.inl ()))) (fun i => v (Sum.inl (Sum.inr i)))}

def absFamilyValueGraph {ι : Type*} (K : ℝ → Set (ι → ℝ))
    (g : ℝ → (ι → ℝ) → ℝ) : Set (((Unit ⊕ ι) ⊕ Unit) → ℝ) :=
  {v | 2 ≤ v (Sum.inl (Sum.inl ())) ∧
    (fun i => v (Sum.inl (Sum.inr i))) ∈ K (v (Sum.inl (Sum.inl ()))) ∧
    v (Sum.inr ()) = |g (v (Sum.inl (Sum.inl ()))) (fun i => v (Sum.inl (Sum.inr i)))|}

theorem absFamilyValueGraph_definable {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    (Set.univ : Set ℝ).Definable Language.ring (absFamilyValueGraph K g) := by
  let e : (Unit ⊕ ι) ⊕ Unit → ((Unit ⊕ ι) ⊕ Unit) ⊕ Unit :=
    Sum.elim (Sum.inl ∘ Sum.inl) (fun _ => Sum.inr ())
  have hnonneg := realPolynomial_nonneg_definable
    (MvPolynomial.X (Sum.inl (Sum.inr ()) : ((Unit ⊕ ι) ⊕ Unit) ⊕ Unit))
  have hsquare := realPolynomial_zero_definable
    ((MvPolynomial.X (Sum.inl (Sum.inr ()) : ((Unit ⊕ ι) ⊕ Unit) ⊕ Unit)) ^ 2 -
      MvPolynomial.X (Sum.inr ()) ^ 2)
  have h := realDefinable_exists ((hG.preimage_comp e).inter (hnonneg.inter hsquare))
  convert h using 1
  ext v
  simp only [absFamilyValueGraph, familyValueGraph, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_preimage, Function.comp_def, e, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.eval_X, map_sub, map_pow, sub_eq_zero]
  constructor
  · rintro ⟨hP, hx, ht⟩
    refine ⟨fun _ => g (v (Sum.inl (Sum.inl ()))) (fun i => v (Sum.inl (Sum.inr i))),
      ⟨hP, hx, rfl⟩, ?_, ?_⟩
    · rw [ht]; exact abs_nonneg _
    · rw [ht, sq_abs]
  · rintro ⟨w, ⟨hP, hx, hw⟩, ht, he⟩
    refine ⟨hP, hx, ?_⟩
    have hsq := (sq_eq_sq_iff_abs_eq_abs _ _).mp he
    simpa only [abs_of_nonneg ht, hw] using hsq

theorem absFamilyMaximum_attained_graph_iff {ι : Type*}
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1}) (P t : ℝ) :
    Sum.elim (fun _ : Unit => P) (fun _ : Unit => t) ∈
      attainedFiberMaximumGraph (absFamilyValueGraph K g) ↔
        2 ≤ P ∧ t = absFamilyMaximum K g P := by
  have h := attainedFiberMaximumGraph_function_iff
    (fun (p : Unit → ℝ) (x : ι → ℝ) => 2 ≤ p () ∧ x ∈ K (p ()))
    (fun (p : Unit → ℝ) (x : ι → ℝ) => |g (p ()) x|) (fun _ => P) t
  simp only [and_assoc] at h
  change (_ ∈ attainedFiberMaximumGraph (absFamilyValueGraph K g) ↔ _) at h
  rw [h]
  constructor
  · rintro ⟨x, hP, hx, ht, hb⟩
    exact ⟨hP, (absFamilyMaximum_eq_iff K g hK hne hg P t hP).mpr
      ⟨x, hx, ht, fun y hy => hb y ⟨hP, hy⟩⟩⟩
  · rintro ⟨hP, ht⟩
    obtain ⟨x, hx, he, hb⟩ := (absFamilyMaximum_eq_iff K g hK hne hg P t hP).mp ht
    exact ⟨x, hP, hx, he, fun y hy => hb y hy.2⟩

theorem absFamilyMaximum_graph_definable {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (absFamilyValueGraph K g)) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))} := by
  convert attainedFiberMaximumGraph_definable hG using 1
  ext v
  have he : Sum.elim (fun _ : Unit => v (Sum.inl ()))
      (fun _ : Unit => v (Sum.inr ())) = v := by
    funext a
    rcases a with ⟨⟩ | ⟨⟩ <;> rfl
  simpa only [he, Set.mem_setOf_eq] using
    (absFamilyMaximum_attained_graph_iff K g hK hne hg (v (Sum.inl ())) (v (Sum.inr ()))).symm

theorem absFamilyMaximum_graph_definable_of_value_graph {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))} := by
  exact absFamilyMaximum_graph_definable K g hK hne hg (absFamilyValueGraph_definable K g hG)

end PaperI

