import PaperILean.SemialgebraicPathOperations
import PaperILean.CurveGermFamilyRescale

/-! Exact reversal and concatenation graphs with the external parameter fixed.
These operations do not construct the input path families. Their pointwise
continuity follows from the existing operation theorem when endpoints match.
Pre-strategy screens: checkpoint_115_graph_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set

def jointUnitPathGraph {ρ κ : Type*} (P : Set (ρ → ℝ))
    (g : (ρ → ℝ) → ℝ → κ → ℝ) : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ) :=
  {z | z ∘ Sum.inl ∈ P ∧ z ∘ Sum.inr ∈ unitPathGraph (g (z ∘ Sum.inl))}

theorem jointUnitPathGraph_fiber {ρ κ : Type*} (P : Set (ρ → ℝ))
    (g : (ρ → ℝ) → ℝ → κ → ℝ) {p : ρ → ℝ} (hp : p ∈ P) :
    projectionFiber (jointUnitPathGraph P g) p = unitPathGraph (g p) := by
  ext z
  simp only [projectionFiber, jointUnitPathGraph, mem_setOf_eq, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, hp, true_and]

theorem jointUnitPathGraph_fiber_offDomain {ρ κ : Type*} (P : Set (ρ → ℝ))
    (g : (ρ → ℝ) → ℝ → κ → ℝ) {p : ρ → ℝ} (hp : p ∉ P) :
    projectionFiber (jointUnitPathGraph P g) p = ∅ := by
  ext z
  simp only [projectionFiber, jointUnitPathGraph, mem_setOf_eq, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, hp, false_and, mem_empty_iff_false]

def jointUnitTimeAffineMap {ρ κ : Type*} (a b : ℝ) :
    ρ ⊕ (Unit ⊕ κ) → MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ :=
  Sum.elim (fun r => MvPolynomial.X (Sum.inl r))
    (Sum.elim (fun _ => MvPolynomial.C a * MvPolynomial.X (Sum.inr (Sum.inl ())) +
      MvPolynomial.C b) (fun k => MvPolynomial.X (Sum.inr (Sum.inr k))))

theorem jointUnitTimeAffineMap_eval {ρ κ : Type*} (a b : ℝ)
    (z : (ρ ⊕ (Unit ⊕ κ)) → ℝ) :
    (fun i => MvPolynomial.eval z (jointUnitTimeAffineMap a b i)) =
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => a*z (Sum.inr (Sum.inl ()))+b)
        (fun k => z (Sum.inr (Sum.inr k)))) := by
  funext i
  rcases i with r | (u | k) <;> simp [jointUnitTimeAffineMap, Function.comp_def]

theorem jointUnitTimeAffine_preimage_semialgebraic {ρ κ : Type*}
    {G : Set ((ρ ⊕ (Unit ⊕ κ)) → ℝ)} (hG : HasPolynomialSignDescription G) (a b : ℝ) :
    HasPolynomialSignDescription {z : (ρ ⊕ (Unit ⊕ κ)) → ℝ |
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => a*z (Sum.inr (Sum.inl ()))+b)
        (fun k => z (Sum.inr (Sum.inr k)))) ∈ G} := by
  simpa only [jointUnitTimeAffineMap_eval] using
    hasPolynomialSignDescription_polynomial_preimage hG (jointUnitTimeAffineMap a b)

theorem jointUnitPathGraph_reverse {ρ κ : Type*} (P : Set (ρ → ℝ))
    (g : (ρ → ℝ) → ℝ → κ → ℝ) :
    jointUnitPathGraph P (fun p => unitPathReverse (g p)) =
      {z : (ρ ⊕ (Unit ⊕ κ)) → ℝ |
        Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => -1*z (Sum.inr (Sum.inl ()))+1)
          (fun k => z (Sum.inr (Sum.inr k)))) ∈ jointUnitPathGraph P g} := by
  ext z
  simp only [jointUnitPathGraph, mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rw [unitPathReverse_graph]
  rfl

theorem jointUnitPathGraph_reverse_semialgebraic {ρ κ : Type*}
    {P : Set (ρ → ℝ)} {g : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    HasPolynomialSignDescription (jointUnitPathGraph P (fun p => unitPathReverse (g p))) := by
  rw [jointUnitPathGraph_reverse]
  exact jointUnitTimeAffine_preimage_semialgebraic hG (-1) 1

theorem jointUnitPathGraph_concat {ρ κ : Type*} (P : Set (ρ → ℝ))
    (g h : (ρ → ℝ) → ℝ → κ → ℝ) :
    jointUnitPathGraph P (fun p => unitPathConcat (g p) (h p)) =
      ({z : (ρ ⊕ (Unit ⊕ κ)) → ℝ | 0 ≤ 1-2*z (Sum.inr (Sum.inl ()))} ∩
        {z | Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => 2*z (Sum.inr (Sum.inl ()))+0)
          (fun k => z (Sum.inr (Sum.inr k)))) ∈ jointUnitPathGraph P g}) ∪
      ({z : (ρ ⊕ (Unit ⊕ κ)) → ℝ | 0 < 2*z (Sum.inr (Sum.inl ()))-1} ∩
        {z | Sum.elim (z ∘ Sum.inl) (Sum.elim (fun _ => 2*z (Sum.inr (Sum.inl ()))+(-1))
          (fun k => z (Sum.inr (Sum.inr k)))) ∈ jointUnitPathGraph P h}) := by
  ext z
  simp only [jointUnitPathGraph, mem_setOf_eq, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    mem_union, mem_inter_iff]
  rw [unitPathConcat_graph]
  simp only [mem_union, mem_inter_iff, mem_setOf_eq, Function.comp_apply]
  tauto

theorem jointUnitPathGraph_concat_semialgebraic {ρ κ : Type*}
    {P : Set (ρ → ℝ)} {g h : (ρ → ℝ) → ℝ → κ → ℝ}
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g))
    (hH : HasPolynomialSignDescription (jointUnitPathGraph P h)) :
    HasPolynomialSignDescription (jointUnitPathGraph P (fun p => unitPathConcat (g p) (h p))) := by
  have hL : HasPolynomialSignDescription
      {z : (ρ ⊕ (Unit ⊕ κ)) → ℝ | 0 ≤ 1-2*z (Sum.inr (Sum.inl ()))} := by
    have h := polynomialSignDetermined_nonneg
      (1-2*MvPolynomial.X (Sum.inr (Sum.inl ())) : MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)
    refine ⟨{1-2*MvPolynomial.X (Sum.inr (Sum.inl ()))},?_⟩
    simpa only [map_sub,map_one,map_mul,map_ofNat,MvPolynomial.eval_X] using h
  have hR : HasPolynomialSignDescription
      {z : (ρ ⊕ (Unit ⊕ κ)) → ℝ | 0 < 2*z (Sum.inr (Sum.inl ()))-1} := by
    have h := polynomialSignDetermined_pos
      (2*MvPolynomial.X (Sum.inr (Sum.inl ()))-1 : MvPolynomial (ρ ⊕ (Unit ⊕ κ)) ℝ)
    refine ⟨{2*MvPolynomial.X (Sum.inr (Sum.inl ()))-1},?_⟩
    simpa only [map_sub,map_one,map_mul,map_ofNat,MvPolynomial.eval_X] using h
  rw [jointUnitPathGraph_concat]
  exact (hL.inter (jointUnitTimeAffine_preimage_semialgebraic hG 2 0)).union
    (hR.inter (jointUnitTimeAffine_preimage_semialgebraic hH 2 (-1)))

theorem jointUnitPathGraph_uniform_fiber_format {ρ κ : Type*}
    (P : Set (ρ → ℝ)) (g : (ρ → ℝ) → ℝ → κ → ℝ)
    (hG : HasPolynomialSignDescription (jointUnitPathGraph P g)) :
    ∃ s d : ℕ, ∀ p ∈ P, ∃ A : Finset (MvPolynomial (Unit ⊕ κ) ℝ),
      A.card ≤ s ∧ (∀ v ∈ A, v.totalDegree ≤ d) ∧ PolynomialSignDetermined A (unitPathGraph (g p)) := by
  obtain ⟨s,d,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format hG
  exact ⟨s,d,fun p hp => by simpa only [jointUnitPathGraph_fiber P g hp] using h p⟩

end PaperI
