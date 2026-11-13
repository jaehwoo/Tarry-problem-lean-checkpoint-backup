import PaperILean.SemialgebraicPathData
import PaperILean.PolynomialSignPullback
import Mathlib.Topology.Piecewise

/-! Actual reversal and concatenation of closed-unit-interval semialgebraic
paths. The midpoint matches the given target/source. Graphs are computed by
polynomial substitution and sign tests, without a new published input.
Pre-strategy evidence: checkpoint_113_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable

theorem HasPolynomialSignDescription.inter {α : Type*}
    {S T : Set (α → ℝ)} (hS : HasPolynomialSignDescription S)
    (hT : HasPolynomialSignDescription T) : HasPolynomialSignDescription (S ∩ T) := by
  obtain ⟨A,hA⟩ := hS
  obtain ⟨B,hB⟩ := hT
  exact ⟨_,polynomialSignDetermined_inter hA hB⟩

theorem HasPolynomialSignDescription.union {α : Type*}
    {S T : Set (α → ℝ)} (hS : HasPolynomialSignDescription S)
    (hT : HasPolynomialSignDescription T) : HasPolynomialSignDescription (S ∪ T) := by
  obtain ⟨A,hA⟩ := hS
  obtain ⟨B,hB⟩ := hT
  exact ⟨_,polynomialSignDetermined_union hA hB⟩

def unitTimeAffineMap {α : Type*} (a b : ℝ) :
    Unit ⊕ α → MvPolynomial (Unit ⊕ α) ℝ :=
  Sum.elim (fun _ => MvPolynomial.C a * MvPolynomial.X (Sum.inl ()) + MvPolynomial.C b)
    (fun i => MvPolynomial.X (Sum.inr i))

theorem unitTimeAffineMap_eval {α : Type*} (a b : ℝ) (v : (Unit ⊕ α) → ℝ) :
    (fun i => MvPolynomial.eval v (unitTimeAffineMap a b i)) =
      Sum.elim (fun _ => a * v (Sum.inl ()) + b) (fun i => v (Sum.inr i)) := by
  funext i
  rcases i with u | i <;> simp [unitTimeAffineMap]

theorem unitTimeAffine_preimage_semialgebraic {α : Type*}
    {G : Set ((Unit ⊕ α) → ℝ)} (hG : HasPolynomialSignDescription G) (a b : ℝ) :
    HasPolynomialSignDescription {v : (Unit ⊕ α) → ℝ |
      Sum.elim (fun _ => a * v (Sum.inl ()) + b) (fun i => v (Sum.inr i)) ∈ G} := by
  simpa only [unitTimeAffineMap_eval] using
    hasPolynomialSignDescription_polynomial_preimage hG (unitTimeAffineMap a b)

def unitPathReverse {α : Type*} (γ : ℝ → α → ℝ) (t : ℝ) : α → ℝ := γ (1-t)

theorem unitPathReverse_graph {α : Type*} (γ : ℝ → α → ℝ) :
    unitPathGraph (unitPathReverse γ) = {v : (Unit ⊕ α) → ℝ |
      Sum.elim (fun _ => -1 * v (Sum.inl ()) + 1) (fun i => v (Sum.inr i)) ∈ unitPathGraph γ} := by
  ext v
  simp only [unitPathGraph, unitPathReverse, mem_setOf_eq, Sum.elim_inl, Sum.elim_inr, mem_Icc]
  have ht : (0 ≤ v (Sum.inl ()) ∧ v (Sum.inl ()) ≤ 1) ↔
      (0 ≤ -1 * v (Sum.inl ()) + 1 ∧ -1 * v (Sum.inl ()) + 1 ≤ 1) := by
    constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith
  rw [ht]
  congr 2
  ring

theorem unitPathReverse_semialgebraic {α : Type*} {γ : ℝ → α → ℝ}
    (hγ : HasPolynomialSignDescription (unitPathGraph γ)) :
    HasPolynomialSignDescription (unitPathGraph (unitPathReverse γ)) := by
  rw [unitPathReverse_graph]
  exact unitTimeAffine_preimage_semialgebraic hγ (-1) 1

def unitPathConcat {α : Type*} (γ η : ℝ → α → ℝ) (t : ℝ) : α → ℝ :=
  if t ≤ 1/2 then γ (2*t) else η (2*t-1)

theorem unitPathConcat_graph {α : Type*} (γ η : ℝ → α → ℝ) :
    unitPathGraph (unitPathConcat γ η) =
      ({v : (Unit ⊕ α) → ℝ | 0 ≤ 1-2*v (Sum.inl ())} ∩
        {v | Sum.elim (fun _ => 2*v (Sum.inl ())+0) (fun i => v (Sum.inr i)) ∈ unitPathGraph γ}) ∪
      ({v : (Unit ⊕ α) → ℝ | 0 < 2*v (Sum.inl ())-1} ∩
        {v | Sum.elim (fun _ => 2*v (Sum.inl ())+(-1)) (fun i => v (Sum.inr i)) ∈ unitPathGraph η}) := by
  ext v
  simp only [unitPathGraph, unitPathConcat, mem_setOf_eq, mem_union, mem_inter_iff,
    Sum.elim_inl, Sum.elim_inr, mem_Icc, add_zero, ← sub_eq_add_neg]
  by_cases h : v (Sum.inl ()) ≤ 1/2
  · rw [if_pos h]
    constructor
    · rintro ⟨⟨h0,h1⟩,hx⟩
      exact Or.inl ⟨by linarith,⟨by linarith,by linarith⟩,hx⟩
    · rintro (⟨_,⟨h0,h1⟩,hx⟩ | ⟨hp,_⟩)
      · exact ⟨⟨by linarith,by linarith⟩,hx⟩
      · linarith
  · rw [if_neg h]
    constructor
    · rintro ⟨⟨h0,h1⟩,hx⟩
      exact Or.inr ⟨by linarith,⟨by linarith,by linarith⟩,hx⟩
    · rintro (⟨hp,_⟩ | ⟨_,⟨h0,h1⟩,hx⟩)
      · linarith
      · exact ⟨⟨by linarith,by linarith⟩,hx⟩

theorem unitPathConcat_semialgebraic {α : Type*} {γ η : ℝ → α → ℝ}
    (hγ : HasPolynomialSignDescription (unitPathGraph γ))
    (hη : HasPolynomialSignDescription (unitPathGraph η)) :
    HasPolynomialSignDescription (unitPathGraph (unitPathConcat γ η)) := by
  have hL : HasPolynomialSignDescription {v : (Unit ⊕ α) → ℝ |
      0 ≤ 1-2*v (Sum.inl ())} := by
    have h := polynomialSignDetermined_nonneg
      (1-2*MvPolynomial.X (Sum.inl ()) : MvPolynomial (Unit ⊕ α) ℝ)
    refine ⟨{1-2*MvPolynomial.X (Sum.inl ())},?_⟩
    simpa only [map_sub, map_one, map_mul, map_ofNat, MvPolynomial.eval_X] using h
  have hR : HasPolynomialSignDescription {v : (Unit ⊕ α) → ℝ |
      0 < 2*v (Sum.inl ())-1} := by
    have h := polynomialSignDetermined_pos
      (2*MvPolynomial.X (Sum.inl ())-1 : MvPolynomial (Unit ⊕ α) ℝ)
    refine ⟨{2*MvPolynomial.X (Sum.inl ())-1},?_⟩
    simpa only [map_sub, map_one, map_mul, map_ofNat, MvPolynomial.eval_X] using h
  rw [unitPathConcat_graph]
  exact (hL.inter (unitTimeAffine_preimage_semialgebraic hγ 2 0)).union
    (hR.inter (unitTimeAffine_preimage_semialgebraic hη 2 (-1)))

theorem unitPathConcat_continuousOn {α : Type*} {γ η : ℝ → α → ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hη : ContinuousOn η (Icc (0 : ℝ) 1)) (hm : γ 1 = η 0) :
    ContinuousOn (unitPathConcat γ η) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.if
  · intro t ht
    have heq : t = 1/2 := frontier_Iic_subset _ ht.2
    subst t
    norm_num
    exact hm
  · apply hγ.comp (continuous_const.mul continuous_id).continuousOn
    rintro t ⟨ht,hb⟩
    have hb' : t ≤ 1/2 := by
      change t ∈ closure (Iic ((1:ℝ)/2)) at hb
      rwa [isClosed_Iic.closure_eq] at hb
    change 0 ≤ 2*t ∧ 2*t ≤ 1
    exact ⟨by linarith [ht.1],by linarith⟩
  · apply hη.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
    rintro t ⟨ht,hb⟩
    have hb' : (1:ℝ)/2 ≤ t := by
      have hset : {a : ℝ | ¬a ≤ 1/2} = Ioi ((1:ℝ)/2) := by
        ext a
        simp only [mem_setOf_eq, mem_Ioi, not_le]
      rwa [hset,closure_Ioi] at hb
    change 0 ≤ 2*t-1 ∧ 2*t-1 ≤ 1
    exact ⟨by linarith,by linarith [ht.2]⟩

def SemialgebraicUnitPath.weaken {α : Type*} {S T : Set (α → ℝ)}
    {a b : α → ℝ} (γ : SemialgebraicUnitPath S a b) (hST : S ⊆ T) :
    SemialgebraicUnitPath T a b :=
  { γ with mapsTo := fun _ ht => hST (γ.mapsTo ht) }

def SemialgebraicUnitPath.reverse {α : Type*} {S : Set (α → ℝ)}
    {a b : α → ℝ} (γ : SemialgebraicUnitPath S a b) : SemialgebraicUnitPath S b a where
  toFun := unitPathReverse γ.toFun
  continuousOn := γ.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
    (by intro t ht; exact ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  mapsTo := by
    intro t ht
    exact γ.mapsTo ⟨by linarith [ht.2],by linarith [ht.1]⟩
  source := by simpa [unitPathReverse] using γ.target
  target := by simpa [unitPathReverse] using γ.source
  semialgebraic := unitPathReverse_semialgebraic γ.semialgebraic

def SemialgebraicUnitPath.trans {α : Type*} {S : Set (α → ℝ)}
    {a b c : α → ℝ} (γ : SemialgebraicUnitPath S a b)
    (η : SemialgebraicUnitPath S b c) : SemialgebraicUnitPath S a c where
  toFun := unitPathConcat γ.toFun η.toFun
  continuousOn := unitPathConcat_continuousOn γ.continuousOn η.continuousOn
    (γ.target.trans η.source.symm)
  mapsTo := by
    intro t ht
    by_cases h : t ≤ 1/2
    · simp only [unitPathConcat, if_pos h]
      exact γ.mapsTo ⟨by linarith [ht.1],by linarith⟩
    · simp only [unitPathConcat, if_neg h]
      exact η.mapsTo ⟨by linarith,by linarith [ht.2]⟩
  source := by simpa [unitPathConcat] using γ.source
  target := by norm_num [unitPathConcat]; exact η.target
  semialgebraic := unitPathConcat_semialgebraic γ.semialgebraic η.semialgebraic

theorem SemialgebraicUnitPath.weaken_toFun {α : Type*} {S T : Set (α → ℝ)}
    {a b : α → ℝ} (γ : SemialgebraicUnitPath S a b) (hST : S ⊆ T) :
    (γ.weaken hST).toFun = γ.toFun := rfl

theorem SemialgebraicUnitPath.reverse_toFun {α : Type*} {S : Set (α → ℝ)}
    {a b : α → ℝ} (γ : SemialgebraicUnitPath S a b) :
    γ.reverse.toFun = unitPathReverse γ.toFun := rfl

theorem SemialgebraicUnitPath.trans_toFun {α : Type*} {S : Set (α → ℝ)}
    {a b c : α → ℝ} (γ : SemialgebraicUnitPath S a b)
    (η : SemialgebraicUnitPath S b c) :
    (γ.trans η).toFun = unitPathConcat γ.toFun η.toFun := rfl

end PaperI
