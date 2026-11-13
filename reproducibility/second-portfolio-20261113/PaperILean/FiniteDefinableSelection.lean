import PaperILean.RealPolynomialDefinability
import PaperILean.PublishedRealAlgebraicAssumptions
import Mathlib.Data.Finset.Max

/-! Finite-valued choice by a disjoint first-eligible partition. The selector
is defined only on the covered domain, including the empty-index case. No
continuity in parameters is claimed. Prerequisite: checkpoint115 obstruction tests. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def firstFiniteEligible {X ι : Type*} (D : ι → Set X) (rank : ι → ℕ) (i : ι) : Set X :=
  {x | x ∈ D i ∧ ∀ j, rank j < rank i → x ∉ D j}

theorem firstFiniteEligible_subset {X ι : Type*} (D : ι → Set X) (rank : ι → ℕ) (i : ι) :
    firstFiniteEligible D rank i ⊆ D i := fun _ h => h.1

theorem firstFiniteEligible_unique {X ι : Type*} {D : ι → Set X} {rank : ι → ℕ}
    (hrank : Function.Injective rank) {x : X} {i j : ι}
    (hi : x ∈ firstFiniteEligible D rank i) (hj : x ∈ firstFiniteEligible D rank j) : i = j := by
  apply hrank
  rcases lt_trichotomy (rank i) (rank j) with h | h | h
  · exact False.elim (hj.2 i h hi.1)
  · exact h
  · exact False.elim (hi.2 j h hj.1)

theorem firstFiniteEligible_exists {X ι : Type*} [Fintype ι]
    (D : ι → Set X) (rank : ι → ℕ) {x : X} (hx : ∃ i, x ∈ D i) :
    ∃ i, x ∈ firstFiniteEligible D rank i := by
  classical
  let E := Finset.univ.filter (fun i => x ∈ D i)
  have hE : E.Nonempty := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := E.exists_min_image rank hE
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  intro j hj hxj
  exact (not_lt_of_ge (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hxj⟩))) hj

theorem firstFiniteEligible_definable {ρ ι : Type*} [Fintype ι]
    (D : ι → Set (ρ → ℝ)) (rank : ι → ℕ)
    (hD : ∀ i, (univ : Set ℝ).Definable Language.ring (D i)) (i : ι) :
    (univ : Set ℝ).Definable Language.ring (firstFiniteEligible D rank i) := by
  classical
  have h : ∀ j : ι, (univ : Set ℝ).Definable Language.ring
      {x : ρ → ℝ | rank j < rank i → x ∉ D j} := by
    intro j
    by_cases hj : rank j < rank i
    · simpa only [hj, true_implies] using (hD j).compl
    · simpa only [hj, false_implies, Set.setOf_true] using
        (Set.definable_univ : (univ : Set ℝ).Definable Language.ring (univ : Set (ρ → ℝ)))
  exact (hD i).inter (realDefinable_finite_all h)

/-- All fibers of this finite-valued selector are definable. The output type
need not be inhabited: the input subtype is empty when no index is available. -/
theorem finite_definable_selector {ρ ι : Type*} [Fintype ι]
    (D : ι → Set (ρ → ℝ))
    (hD : ∀ i, (univ : Set ℝ).Definable Language.ring (D i)) :
    ∃ pick : {p : ρ → ℝ // ∃ i, p ∈ D i} → ι,
      (∀ p, p.val ∈ D (pick p)) ∧
      ∀ i, (univ : Set ℝ).Definable Language.ring
        {p : ρ → ℝ | ∃ hp : ∃ j, p ∈ D j, pick ⟨p,hp⟩ = i} := by
  classical
  let rank : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have hrank : Function.Injective rank := by
    intro i j h
    exact (Fintype.equivFin ι).injective (Fin.ext h)
  have hex : ∀ p : {p : ρ → ℝ // ∃ i, p ∈ D i}, ∃ i, p.val ∈ firstFiniteEligible D rank i :=
    fun p => firstFiniteEligible_exists D rank p.property
  choose pick hpick using hex
  refine ⟨pick,fun p => (hpick p).1,?_⟩
  intro i
  convert firstFiniteEligible_definable D rank hD i using 1
  ext p
  constructor
  · rintro ⟨hp,h⟩
    simpa only [h] using hpick ⟨p,hp⟩
  · intro hp
    refine ⟨⟨i,hp.1⟩,?_⟩
    exact firstFiniteEligible_unique hrank (hpick ⟨p,⟨i,hp.1⟩⟩) hp

/-- Restrict the finite selector to a separately specified definable domain.
Only coverage on that domain is required; candidates may exist elsewhere. -/
theorem finite_definable_selector_on {ρ ι : Type*} [Fintype ι]
    (U : Set (ρ → ℝ)) (D : ι → Set (ρ → ℝ))
    (hU : (univ : Set ℝ).Definable Language.ring U)
    (hD : ∀ i, (univ : Set ℝ).Definable Language.ring (D i))
    (hcover : ∀ p ∈ U, ∃ i, p ∈ D i) :
    ∃ pick : U → ι, (∀ p, p.val ∈ D (pick p)) ∧
      ∀ i, (univ : Set ℝ).Definable Language.ring
        {p : ρ → ℝ | ∃ hp : p ∈ U, pick ⟨p,hp⟩ = i} := by
  classical
  obtain ⟨pick,hpick,hfiber⟩ := finite_definable_selector (fun i => U ∩ D i)
    (fun i => hU.inter (hD i))
  let lift : U → {p : ρ → ℝ // ∃ i, p ∈ U ∩ D i} := fun p =>
    ⟨p.val,by obtain ⟨i,hi⟩ := hcover p.val p.property; exact ⟨i,p.property,hi⟩⟩
  refine ⟨pick ∘ lift,fun p => (hpick (lift p)).2,?_⟩
  intro i
  convert hfiber i using 1
  ext p
  constructor
  · rintro ⟨hp,hi⟩
    exact ⟨(lift ⟨p,hp⟩).property,hi⟩
  · rintro ⟨hp,hi⟩
    obtain ⟨j,hj⟩ := hp
    exact ⟨hj.1,hi⟩

end PaperI
