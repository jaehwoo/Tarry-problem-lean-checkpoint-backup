import PaperILean.GoodStripOpenSections
import PaperILean.GoodStripQuantitative
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

noncomputable section

namespace PaperI.GoodStrips

open Set FirstOrder Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private abbrev RD {α : Type} (S : Set (α → ℝ)) :=
  (univ : Set ℝ).Definable Language.ring S

abbrev ScalarParameters (κ : Type) (s d : ℕ) := Fin s × (κ → Fin (d+1))
abbrev SignTable (s : ℕ) := (Fin s → Bool × Bool) → Bool

theorem signFormat_universal {κ : Type} [Fintype κ] (s d : ℕ)
    (S : Set (κ → ℝ)) (A : Finset (MvPolynomial κ ℝ)) (hAc : A.card ≤ s)
    (hAd : ∀ q ∈ A, q.totalDegree ≤ d) (hA : PolynomialSignDetermined A S) :
    ∃ (b : SignTable s) (p : ScalarParameters κ s d → ℝ),
      ∀ v, Sum.elim p v ∈ universalPolynomialBooleanSet κ s d b ↔ v ∈ S := by
  obtain ⟨r,hr,hS⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s d hAc hAd hA
  obtain ⟨b,hb⟩ := polynomialSignDetermined_exists_universal_fiber s d r hr S hS
  refine ⟨b,polynomialFamilyCoefficients d r,fun v => ?_⟩
  rw [hb]
  rfl

def parameterPlaneLift {ρ α : Type} (e : ρ → α) (A : Set (ρ ⊕ Fin 2 → ℝ)) :
    Set (α ⊕ Fin 2 → ℝ) := {v | v ∘ Sum.map e id ∈ A}

def parameterGraphLift {ρ α : Type} (e : ρ → α) (G : Set (ρ ⊕ Fin 3 → ℝ)) :
    Set (α ⊕ Fin 3 → ℝ) := {v | v ∘ Sum.map e id ∈ G}

theorem parameterPlaneLift_definable {ρ α : Type} (e : ρ → α)
    {A : Set (ρ ⊕ Fin 2 → ℝ)} (hA : RD A) : RD (parameterPlaneLift e A) :=
  hA.preimage_comp _

theorem parameterGraphLift_definable {ρ α : Type} (e : ρ → α)
    {G : Set (ρ ⊕ Fin 3 → ℝ)} (hG : RD G) : RD (parameterGraphLift e G) :=
  hG.preimage_comp _

theorem parameterPlaneLift_fiber {ρ α : Type} (e : ρ → α)
    (A : Set (ρ ⊕ Fin 2 → ℝ)) (p : α → ℝ) :
    planeFiber (parameterPlaneLift e A) p = planeFiber A (p ∘ e) := by
  ext x
  have he : Sum.elim p ![x.1,x.2] ∘ Sum.map e id = Sum.elim (p ∘ e) ![x.1,x.2] := by
    funext i
    cases i <;> rfl
  simp [planeFiber,parameterPlaneLift,he]

theorem parameterGraphLift_value {ρ α : Type} (e : ρ → α)
    (G : Set (ρ ⊕ Fin 3 → ℝ)) (p : α → ℝ) (x : ℝ × ℝ) (z : ℝ) :
    Sum.elim p ![x.1,x.2,z] ∈ parameterGraphLift e G ↔
      Sum.elim (p ∘ e) ![x.1,x.2,z] ∈ G := by
  have he : Sum.elim p ![x.1,x.2,z] ∘ Sum.map e id = Sum.elim (p ∘ e) ![x.1,x.2,z] := by
    funext i
    cases i <;> rfl
  simp [parameterGraphLift,he]

def boxFamily {α : Type} (x0 x1 y0 y1 : α) : Set (α ⊕ Fin 2 → ℝ) :=
  {v | (v (Sum.inr 0),v (Sum.inr 1)) ∈ Rect
    (v (Sum.inl x0)) (v (Sum.inl x1)) (v (Sum.inl y0)) (v (Sum.inl y1))}

theorem boxFamily_definable {α : Type} [Finite α] (x0 x1 y0 y1 : α) :
    RD (boxFamily x0 x1 y0 y1) := by
  let X : α ⊕ Fin 2 → MvPolynomial (α ⊕ Fin 2) ℝ := MvPolynomial.X
  convert ((realPolynomial_lt_definable (X (Sum.inl x0)) (X (Sum.inr 0))).inter
    (realPolynomial_lt_definable (X (Sum.inr 0)) (X (Sum.inl x1)))).inter
    ((realPolynomial_lt_definable (X (Sum.inl y0)) (X (Sum.inr 1))).inter
    (realPolynomial_lt_definable (X (Sum.inr 1)) (X (Sum.inl y1)))) using 1
  ext v
  simp only [boxFamily,mem_setOf_eq,mem_prod,mem_Ioo,mem_inter_iff,X,MvPolynomial.eval_X]

theorem boxFamily_fiber {α : Type} (x0 x1 y0 y1 : α) (p : α → ℝ) :
    planeFiber (boxFamily x0 x1 y0 y1) p = Rect (p x0) (p x1) (p y0) (p y1) := by
  ext x
  simp [boxFamily,planeFiber]

theorem planeFiber_inter {α : Type} (A B : Set (α ⊕ Fin 2 → ℝ)) (p : α → ℝ) :
    planeFiber (A ∩ B) p = planeFiber A p ∩ planeFiber B p := by
  ext x
  rfl

def graphDomainCut {α : Type} (A : Set (α ⊕ Fin 2 → ℝ))
    (G : Set (α ⊕ Fin 3 → ℝ)) : Set (α ⊕ Fin 3 → ℝ) :=
  G ∩ {v | Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0),v (Sum.inr 1)] ∈ A}

theorem graphDomainCut_definable {α : Type} {A : Set (α ⊕ Fin 2 → ℝ)}
    {G : Set (α ⊕ Fin 3 → ℝ)} (hA : RD A) (hG : RD G) : RD (graphDomainCut A G) := by
  let e : α ⊕ Fin 2 → α ⊕ Fin 3 := Sum.elim Sum.inl ![Sum.inr 0,Sum.inr 1]
  convert hG.inter (hA.preimage_comp e) using 1
  ext v
  have he : v ∘ e = Sum.elim (v ∘ Sum.inl) ![v (Sum.inr 0),v (Sum.inr 1)] := by
    funext i
    rcases i with i | i
    · rfl
    · fin_cases i <;> rfl
  simp [graphDomainCut,he]

theorem scalarGraph_sign_of_realizesOn {α : Type} [Finite α]
    (hQE : PublishedRealSemialgebraicity) {A : Set (α ⊕ Fin 2 → ℝ)}
    {G : Set (α ⊕ Fin 3 → ℝ)} (hA : RD A) (hG : RD G)
    (p : α → ℝ) (f : ℝ × ℝ → ℝ) (hf : RealizesOn G p f (planeFiber A p)) :
    HasPolynomialSignDescription (scalarGraph f (planeFiber A p)) := by
  obtain ⟨F,hF⟩ := hQE.finite_sign_description _ (graphDomainCut_definable hA hG)
  have h := polynomialSignDetermined_projectionFiber p F _ hF
  have he : projectionFiber (graphDomainCut A G) p = scalarGraph f (planeFiber A p) := by
    ext v
    have hv : ![v 0,v 1,v 2] = v := by funext i; fin_cases i <;> rfl
    change ((Sum.elim p v ∈ G) ∧ (v 0,v 1) ∈ planeFiber A p) ↔
      (v 0,v 1) ∈ planeFiber A p ∧ v 2 = f (v 0,v 1)
    rw [and_comm]
    apply and_congr_right
    intro hp
    simpa only [hv] using hf (v 0,v 1) hp (v 2)
  exact ⟨_,he ▸ h⟩

end PaperI.GoodStrips
