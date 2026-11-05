import PaperILean.CurveSelectionRescale
import PaperILean.SemialgebraicRelationComposition

/-! Rescale one supplied joint graph, retaining every parameter coordinate.
Pointwise semialgebraicity of curve germs does not supply joint semialgebraicity.
The bounds here depend on the supplied joint graph and precede p and delta.
No joint existence theorem, continuity in the parameters, or ambient-format
bound for constructing the input germs is asserted. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable

def jointGermRescaleMap {ρ α : Type*} :
    ρ ⊕ (Unit ⊕ α) → MvPolynomial ((ρ ⊕ Unit) ⊕ (Unit ⊕ α)) ℝ :=
  Sum.elim (fun i => MvPolynomial.X (Sum.inl (Sum.inl i)))
    (Sum.elim (fun _ => MvPolynomial.X (Sum.inl (Sum.inr ())) *
      MvPolynomial.X (Sum.inr (Sum.inl ())))
      (fun i => MvPolynomial.X (Sum.inr (Sum.inr i))))

def jointGermRescaledGraph {ρ α : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)) :
    Set (((ρ ⊕ Unit) ⊕ (Unit ⊕ α)) → ℝ) :=
  {v | v (Sum.inr (Sum.inl ())) ∈ Icc (0 : ℝ) 1 ∧
    Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
      (Sum.elim (fun _ => v (Sum.inl (Sum.inr ())) * v (Sum.inr (Sum.inl ())))
        (fun i => v (Sum.inr (Sum.inr i)))) ∈ G}

theorem jointGermRescaleMap_eval {ρ α : Type*}
    (v : ((ρ ⊕ Unit) ⊕ (Unit ⊕ α)) → ℝ) :
    (fun i => MvPolynomial.eval v (jointGermRescaleMap i)) =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
        (Sum.elim (fun _ => v (Sum.inl (Sum.inr ())) * v (Sum.inr (Sum.inl ())))
          (fun i => v (Sum.inr (Sum.inr i)))) := by
  funext i
  rcases i with i | (u | i) <;> simp [jointGermRescaleMap]

theorem jointGermRescaledGraph_eq_polynomial_preimage {ρ α : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)) :
    jointGermRescaledGraph G =
      ({v | 0 ≤ MvPolynomial.eval v (MvPolynomial.X (Sum.inr (Sum.inl ())))} ∩
        {v | 0 ≤ MvPolynomial.eval v (1 - MvPolynomial.X (Sum.inr (Sum.inl ())))}) ∩
      {v | (fun i => MvPolynomial.eval v (jointGermRescaleMap i)) ∈ G} := by
  ext v
  simp only [jointGermRescaledGraph, mem_setOf_eq, mem_inter_iff, MvPolynomial.eval_X,
    map_sub, map_one, sub_nonneg, jointGermRescaleMap_eval, mem_Icc]

theorem jointGermRescaledGraph_semialgebraic {ρ α : Type*}
    {G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)} (hG : HasPolynomialSignDescription G) :
    HasPolynomialSignDescription (jointGermRescaledGraph G) := by
  classical
  obtain ⟨A,hA⟩ := hasPolynomialSignDescription_polynomial_preimage hG jointGermRescaleMap
  rw [jointGermRescaledGraph_eq_polynomial_preimage]
  exact ⟨_, polynomialSignDetermined_inter
    (polynomialSignDetermined_inter
      (polynomialSignDetermined_nonneg (MvPolynomial.X (Sum.inr (Sum.inl ()))))
      (polynomialSignDetermined_nonneg (1 - MvPolynomial.X (Sum.inr (Sum.inl ()))))) hA⟩

theorem jointGermRescaledGraph_fiber_mem {ρ α : Type*}
    (G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)) (p : ρ → ℝ) (δ t : ℝ) (x : α → ℝ) :
    Sum.elim (fun _ => t) x ∈
      projectionFiber (jointGermRescaledGraph G) (Sum.elim p (fun _ => δ)) ↔
      t ∈ Icc (0 : ℝ) 1 ∧ Sum.elim p (Sum.elim (fun _ => δ*t) x) ∈ G := Iff.rfl

theorem jointGermRescaledGraph_uniform_fiber_format {ρ α : Type*}
    {G : Set ((ρ ⊕ (Unit ⊕ α)) → ℝ)} (hG : HasPolynomialSignDescription G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (δ : ℝ),
      ∃ A : Finset (MvPolynomial (Unit ⊕ α) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A
          (projectionFiber (jointGermRescaledGraph G) (Sum.elim p (fun _ => δ))) := by
  obtain ⟨s,D,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (jointGermRescaledGraph_semialgebraic hG)
  exact ⟨s,D,fun p δ => h (Sum.elim p (fun _ => δ))⟩

def halfOpenPathGraphFamily {ρ α : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ) :
    Set ((ρ ⊕ (Unit ⊕ α)) → ℝ) :=
  {v | (fun i => v (Sum.inl i)) ∈ P ∧
    (fun i => v (Sum.inr i)) ∈
      halfOpenPathGraph (ε (fun i => v (Sum.inl i))) (γ (fun i => v (Sum.inl i)))}

theorem halfOpenPathGraphFamily_fiber {ρ α : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) :
    projectionFiber (halfOpenPathGraphFamily P ε γ) p = halfOpenPathGraph (ε p) (γ p) := by
  ext v
  exact ⟨fun h => h.2, fun h => ⟨hp,h⟩⟩

theorem halfOpenPathGraphFamily_fiber_offDomain {ρ α : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    {p : ρ → ℝ} (hp : p ∉ P) :
    projectionFiber (halfOpenPathGraphFamily P ε γ) p = ∅ := by
  ext v
  exact ⟨fun h => (hp h.1).elim, fun h => h.elim⟩

theorem halfOpenPathGraphFamily_rescaled_fiber {ρ α : Type*} (P : Set (ρ → ℝ))
    (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    {p : ρ → ℝ} (hp : p ∈ P) {δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < ε p) :
    projectionFiber (jointGermRescaledGraph (halfOpenPathGraphFamily P ε γ))
      (Sum.elim p (fun _ => δ)) = unitPathGraph (fun t => γ p (δ*t)) := by
  ext v
  change (v (Sum.inl ()) ∈ Icc (0 : ℝ) 1 ∧ p ∈ P ∧
    δ * v (Sum.inl ()) ∈ Ico (0 : ℝ) (ε p) ∧
    (fun i => v (Sum.inr i)) = γ p (δ * v (Sum.inl ()))) ↔ _
  constructor
  · rintro ⟨ht,_,_,hx⟩
    exact ⟨ht,hx⟩
  · rintro ⟨ht,hx⟩
    exact ⟨ht,hp,mul_unitInterval_mem_Ico hδ hδε ht,hx⟩

theorem halfOpenPathGraphFamily_rescaled_fiber_offDomain {ρ α : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    {p : ρ → ℝ} (hp : p ∉ P) (δ : ℝ) :
    projectionFiber (jointGermRescaledGraph (halfOpenPathGraphFamily P ε γ))
      (Sum.elim p (fun _ => δ)) = ∅ := by
  ext v
  exact ⟨fun h => (hp h.2.1).elim, fun h => h.elim⟩

theorem halfOpenPathGraphFamily_uniform_rescale_format {ρ α : Type*}
    (P : Set (ρ → ℝ)) (ε : (ρ → ℝ) → ℝ) (γ : (ρ → ℝ) → ℝ → α → ℝ)
    (hG : HasPolynomialSignDescription (halfOpenPathGraphFamily P ε γ)) :
    ∃ s D : ℕ, ∀ p ∈ P, ∀ δ : ℝ, 0 ≤ δ → δ < ε p →
      ∃ A : Finset (MvPolynomial (Unit ⊕ α) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
          PolynomialSignDetermined A (unitPathGraph (fun t => γ p (δ*t))) := by
  obtain ⟨s,D,h⟩ := jointGermRescaledGraph_uniform_fiber_format hG
  refine ⟨s,D,?_⟩
  intro p hp δ hδ hδε
  simpa only [halfOpenPathGraphFamily_rescaled_fiber P ε γ hp hδ hδε] using h p δ

/-- A family of actual germs supplies the individual continuity and endpoint
facts. The joint graph premise remains explicit; it is not inferred from g. -/
theorem semialgebraicCurveGerm_family_uniform_rescale_format {ρ α : Type*}
    (P : Set (ρ → ℝ)) (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p, SemialgebraicCurveGerm (C p) (a p))
    (hG : HasPolynomialSignDescription
      (halfOpenPathGraphFamily P (fun p => (g p).radius) (fun p => (g p).toFun))) :
    ∃ s D : ℕ, ∀ p ∈ P, ∀ δ : ℝ, 0 < δ → δ < (g p).radius →
      ∃ η : SemialgebraicUnitPath (C p ∪ {a p}) (a p) ((g p).toFun δ),
        η.toFun = (g p).rescale δ ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ α) ℝ), A.card ≤ s ∧
          (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A (unitPathGraph η.toFun) := by
  obtain ⟨s,D,h⟩ := halfOpenPathGraphFamily_uniform_rescale_format P
    (fun p => (g p).radius) (fun p => (g p).toFun) hG
  refine ⟨s,D,?_⟩
  intro p hp δ hδ hδε
  refine ⟨(g p).toUnitPath δ hδ hδε,rfl,?_⟩
  exact h p hp δ hδ.le hδε

/-- The exact domain variant requires germs only for parameters in P. -/
def curveGermFamilyGraph {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val)) :
    Set ((ρ ⊕ (Unit ⊕ α)) → ℝ) :=
  {v | ∃ hp : (fun i => v (Sum.inl i)) ∈ P,
    (fun i => v (Sum.inr i)) ∈
      halfOpenPathGraph (g ⟨_,hp⟩).radius (g ⟨_,hp⟩).toFun}

theorem curveGermFamilyGraph_fiber {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val)) (p : P) :
    projectionFiber (curveGermFamilyGraph P C a g) p.val =
      halfOpenPathGraph (g p).radius (g p).toFun := by
  ext v
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨p.property,h⟩⟩

theorem curveGermFamilyGraph_fiber_offDomain {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val))
    {p : ρ → ℝ} (hp : p ∉ P) :
    projectionFiber (curveGermFamilyGraph P C a g) p = ∅ := by
  ext v
  exact ⟨fun ⟨h,_⟩ => (hp h).elim, fun h => h.elim⟩

theorem curveGermFamilyGraph_rescaled_fiber {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val)) (p : P)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδε : δ < (g p).radius) :
    projectionFiber (jointGermRescaledGraph (curveGermFamilyGraph P C a g))
      (Sum.elim p.val (fun _ => δ)) = unitPathGraph ((g p).rescale δ) := by
  ext v
  change (v (Sum.inl ()) ∈ Icc (0 : ℝ) 1 ∧ ∃ hp : p.val ∈ P,
    δ * v (Sum.inl ()) ∈ Ico (0 : ℝ) (g ⟨p.val,hp⟩).radius ∧
    (fun i => v (Sum.inr i)) = (g ⟨p.val,hp⟩).toFun (δ * v (Sum.inl ()))) ↔ _
  constructor
  · rintro ⟨ht,_,_,hx⟩
    exact ⟨ht,hx⟩
  · rintro ⟨ht,hx⟩
    exact ⟨ht,p.property,mul_unitInterval_mem_Ico hδ hδε ht,hx⟩

theorem curveGermFamilyGraph_rescaled_fiber_offDomain {ρ α : Type*}
    (P : Set (ρ → ℝ)) (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val))
    {p : ρ → ℝ} (hp : p ∉ P) (δ : ℝ) :
    projectionFiber (jointGermRescaledGraph (curveGermFamilyGraph P C a g))
      (Sum.elim p (fun _ => δ)) = ∅ := by
  ext v
  exact ⟨fun ⟨_,h,_⟩ => (hp h).elim, fun h => h.elim⟩

/-- The family and its joint finite-sign description are inputs. The same
budgets work for all domain parameters and every strictly interior cutoff. -/
theorem curveGermFamily_uniform_unitPaths {ρ α : Type*} (P : Set (ρ → ℝ))
    (C : (ρ → ℝ) → Set (α → ℝ)) (a : (ρ → ℝ) → α → ℝ)
    (g : ∀ p : P, SemialgebraicCurveGerm (C p.val) (a p.val))
    (hG : HasPolynomialSignDescription (curveGermFamilyGraph P C a g)) :
    ∃ s D : ℕ, ∀ p : P, ∀ δ : ℝ, 0 < δ → δ < (g p).radius →
      ∃ η : SemialgebraicUnitPath (C p.val ∪ {a p.val}) (a p.val) ((g p).toFun δ),
        η.toFun = (g p).rescale δ ∧
        ∃ A : Finset (MvPolynomial (Unit ⊕ α) ℝ), A.card ≤ s ∧
          (∀ q ∈ A, q.totalDegree ≤ D) ∧ PolynomialSignDetermined A (unitPathGraph η.toFun) := by
  obtain ⟨s,D,h⟩ := jointGermRescaledGraph_uniform_fiber_format hG
  refine ⟨s,D,?_⟩
  intro p δ hδ hδε
  refine ⟨(g p).toUnitPath δ hδ hδε,rfl,?_⟩
  simpa only [curveGermFamilyGraph_rescaled_fiber P C a g p hδ.le hδε] using h p.val δ

end PaperI
