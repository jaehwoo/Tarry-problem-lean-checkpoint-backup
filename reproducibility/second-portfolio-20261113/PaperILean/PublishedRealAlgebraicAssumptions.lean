import PaperILean.StoppedMinimumPowerLower
import PaperILean.FamilyMaximumPowerUpper
import PaperILean.FamilyMaximumFirstOrderGraph

/-! Explicit published-input interface for the qualitative real-algebraic step.

The accepted external input is the finite-polynomial-sign consequence of
real quantifier elimination (Basu--Pollack--Roy, Theorem 2.77 and Corollary 2.78).
The input below is actual mathlib ring-language definability over the reals,
with real parameters. It is not a claim that the pure ring language itself
eliminates quantifiers: its formulas are interpreted in the ordered-field
language, whose output is a finite Boolean combination of polynomial signs.
Finite coordinate types can be identified with real affine spaces. No bound
for the number or degrees of output polynomials is part of this interface.

The structure is an explicit proposition-valued theorem parameter, not an
axiom, instance, or supplied proof of the external theorem. Every downstream
result retains that parameter. Standard-only `#print axioms` output verifies
these implications and does not certify the external input inside Lean.

Pre-strategy evidence: evidence/published_real_algebraic_pre_strategy.json.
The checks retain signs rather than only zero loci, one common quantified
witness, degree drops, repeated roots, empty and nonattaining fibers, and the
need for compact bounded total windows. No adequacy of a previously proposed
elimination candidate is assumed. Local graph identifications, positivity,
compactness and all constant/parameter quantifiers are supplied by the checked
project declarations or remain explicit hypotheses below.
-/

noncomputable section
open FirstOrder
namespace PaperI
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- Qualitative published QE input, stated in the exact encodings used here.
This proposition has no provided inhabitant in this module. -/
structure PublishedRealSemialgebraicity : Prop where
  finite_sign_description : ∀ {α : Type} [Finite α] (S : Set (α → ℝ)),
    (Set.univ : Set ℝ).Definable Language.ring S → HasPolynomialSignDescription S

/-- The accepted input preserves the actual projection relation and quantifier
order; no per-atom witnesses replace the common witness. -/
theorem published_real_projection_has_sign_description
    (hQE : PublishedRealSemialgebraicity)
    {α β : Type} [Finite α] [Finite β] {S : Set ((α ⊕ β) → ℝ)}
    (hS : (Set.univ : Set ℝ).Definable Language.ring S) :
    HasPolynomialSignDescription {v : α → ℝ | ∃ w : β → ℝ, Sum.elim v w ∈ S} :=
  hQE.finite_sign_description _ (realDefinable_exists hS)

theorem published_stoppedNormalMinimum_sign_description
    (hQE : PublishedRealSemialgebraicity) (k : ℕ) :
    HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedNormalMinimum k (v (Sum.inl ()))} :=
  hQE.finite_sign_description _ (stoppedNormalMinimum_graph_definable k)

theorem published_stoppedFourthMinimum_sign_description
    (hQE : PublishedRealSemialgebraicity) (k : ℕ) :
    HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = stoppedFourthMinimum k (v (Sum.inl ()))} :=
  hQE.finite_sign_description _ (stoppedFourthMinimum_graph_definable k)

theorem published_stoppedNormalMinimum_rpow_lower
    (hQE : PublishedRealSemialgebraicity) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ stoppedNormalMinimum k P :=
  stoppedNormalMinimum_rpow_lower_of_sign_description k
    (published_stoppedNormalMinimum_sign_description hQE k)

theorem published_stoppedFourthMinimum_rpow_lower
    (hQE : PublishedRealSemialgebraicity) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ stoppedFourthMinimum k P :=
  stoppedFourthMinimum_rpow_lower_of_sign_description k
    (published_stoppedFourthMinimum_sign_description hQE k)

/-- One exponent is chosen before the radius and the actual stopped state. -/
theorem published_stopped_normal_fourth_rpow_lower
    (hQE : PublishedRealSemialgebraicity) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ S : AugmentedState k,
      AugmentedTranslationStopped P S →
        P ^ (-C) ≤ normalOrbitSingularValues k S 2 ∧
        P ^ (-C) ≤ augmentedOrbitSingularValues k S 3 :=
  stopped_normal_fourth_rpow_lower_of_sign_descriptions k
    (published_stoppedNormalMinimum_sign_description hQE k)
    (published_stoppedFourthMinimum_sign_description hQE k)

/-- The bounded-window lower premise is retained explicitly: positivity and a
finite sign graph alone do not control limits at finite parameter values. -/
theorem published_positive_definable_graph_rpow_lower
    (hQE : PublishedRealSemialgebraicity)
    (m : ℝ → ℝ) (hpos : ∀ P : ℝ, 2 ≤ P → 0 < m P)
    (hwindow : ∀ T : ℝ, ∃ b : ℝ, 0 < b ∧
      ∀ P : ℝ, 2 ≤ P → P ≤ T → b ≤ m P)
    (hgraph : (Set.univ : Set ℝ).Definable Language.ring
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = m (v (Sum.inl ()))}) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → P ^ (-C) ≤ m P :=
  positive_sign_graph_rpow_lower m hpos hwindow (hQE.finite_sign_description _ hgraph)

/-- Local project lemmas identify the attained maximum's exact graph from the
actual value graph; QE is used only after that identification. -/
theorem published_absFamilyMaximum_sign_description
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    HasPolynomialSignDescription
      {v : Unit ⊕ Unit → ℝ | 2 ≤ v (Sum.inl ()) ∧
        v (Sum.inr ()) = absFamilyMaximum K g (v (Sum.inl ()))} :=
  hQE.finite_sign_description _
    (absFamilyMaximum_graph_definable_of_value_graph K g hK hne hg hG)

theorem published_absFamilyMaximum_rpow_upper
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → absFamilyMaximum K g P ≤ C * P ^ C :=
  absFamilyMaximum_rpow_upper_of_sign_description K g hK hne hcompact hg
    (published_absFamilyMaximum_sign_description hQE K g hK hne hg hG)

theorem published_continuous_family_rpow_upper
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hcompact : ∀ T : ℝ, IsCompact (parameterFamilyWindow K T))
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, |g P x| ≤ C * P ^ C :=
  continuous_family_rpow_upper_of_sign_description K g hK hne hcompact hg
    (published_absFamilyMaximum_sign_description hQE K g hK hne hg hG)

/-- The manuscript's closed bounded-window and polynomial coordinate conditions
supply the compact windows; they are not hidden in the published QE input. -/
theorem published_polynomially_bounded_family_rpow_upper
    (hQE : PublishedRealSemialgebraicity)
    {ι : Type*} [Finite ι]
    (K : ℝ → Set (ι → ℝ)) (g : ℝ → (ι → ℝ) → ℝ)
    (hK : ∀ P : ℝ, 2 ≤ P → IsCompact (K P))
    (hne : ∀ P : ℝ, 2 ≤ P → (K P).Nonempty)
    (hclosed : ∀ T : ℝ, IsClosed (parameterFamilyWindow K T))
    (A : ℝ) (hA : 0 ≤ A) (N : ℕ)
    (hcoord : ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, ∀ i, |x i| ≤ A * P ^ N)
    (hg : ContinuousOn (fun z : ℝ × (ι → ℝ) => g z.1 z.2)
      {z | 2 ≤ z.1 ∧ z.2 ∈ K z.1})
    (hG : (Set.univ : Set ℝ).Definable Language.ring (familyValueGraph K g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ x ∈ K P, |g P x| ≤ C * P ^ C :=
  polynomially_bounded_family_rpow_upper_of_sign_description K g hK hne
    hclosed A hA N hcoord hg
    (published_absFamilyMaximum_sign_description hQE K g hK hne hg hG)

end PaperI
