import PaperILean.OriginalPreparationSuperlevels

/-! I1263: the simultaneous strict derivative good set has a uniform number
of components. Hardt is applied to this complete parameter family, including
every threshold, not separately to its defining inequalities. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
local instance goodComponentFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.typeDecidableEq _
set_option maxHeartbeats 1000000

def strictDerivativeGoodSet (f : ℝ → ℝ) (N : ℕ) (a b : ℝ)
    (T : Fin (N+1) → ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ∀ n : Fin (N+1), |iteratedDeriv n.val f x| < T n}

def derivativeGoodRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) (N : ℕ) :
    Set (((α ⊕ (Fin 2 ⊕ Fin (N+1))) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr (Sum.inl 0))))
      (v (Sum.inl (Sum.inr (Sum.inl 1)))) ∧
    ∀ n : Fin (N+1), ∃ y : Unit → ℝ,
      Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr ()),y ()] ∈
        iteratedGraphDerivativeRelation G n.val ∧
      -v (Sum.inl (Sum.inr (Sum.inr n))) < y () ∧
        y () < v (Sum.inl (Sum.inr (Sum.inr n)))}

theorem derivativeGoodRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    (univ : Set ℝ).Definable Language.ring (derivativeGoodRelation G N) := by
  let β := (α ⊕ (Fin 2 ⊕ Fin (N+1))) ⊕ Unit
  let e : α ⊕ Fin 2 → β ⊕ Unit := Sum.elim
    (fun c => Sum.inl (Sum.inl (Sum.inl c)))
    (fun i => if i=0 then Sum.inl (Sum.inr ()) else Sum.inr ())
  have hvalue (n : Fin (N+1)) :
      (univ : Set ℝ).Definable Language.ring
      {v : β → ℝ | ∃ y : Unit → ℝ,
        Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr ()),y ()] ∈
          iteratedGraphDerivativeRelation G n.val ∧
        -v (Sum.inl (Sum.inr (Sum.inr n))) < y () ∧
          y () < v (Sum.inl (Sum.inr (Sum.inr n)))} := by
    let q : MvPolynomial (β ⊕ Unit) ℝ :=
      MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (Sum.inr n))))
    let y : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inr ())
    have h := realDefinable_exists (((iteratedGraphDerivativeRelation_definable hG n.val).preimage_comp e).inter ((realPolynomial_lt_definable (-q) y).inter
        (realPolynomial_lt_definable y q)))
    convert h using 1
    ext v
    have he (w : Unit → ℝ) : Sum.elim v w ∘ e =
        Sum.elim (fun c => v (Sum.inl (Sum.inl c))) ![v (Sum.inr ()),w ()] := by
      funext z
      rcases z with z | i
      · rfl
      · fin_cases i <;> simp [e,Function.comp_def]
    simp only [mem_setOf_eq,mem_inter_iff,mem_preimage,he,q,y,
      map_neg,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr]
  exact ((realCoordinate_lt_definable (Sum.inl (Sum.inr (Sum.inl 0))) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr (Sum.inl 1))))).inter
      (realDefinable_finite_all hvalue)

theorem derivativeGoodRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ)
    (a b : ℝ) (N : ℕ) (T : Fin (N+1) → ℝ)
    (hrep : ∀ x ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![x,y] ∈ G ↔ y=f x)
    (hf : ContDiffOn ℝ N f (Ioo a b)) (x : ℝ) :
    Sum.elim (Sum.elim p (Sum.elim ![a,b] T)) (fun _ => x) ∈
      derivativeGoodRelation G N ↔ x ∈ strictDerivativeGoodSet f N a b T := by
  change (x ∈ Ioo a b ∧ ∀ n : Fin (N+1), ∃ y : Unit → ℝ, _ ∧
    -T n < y () ∧ y () < T n) ↔ (x ∈ Ioo a b ∧ ∀ n : Fin (N+1), _)
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro n
  have hr := iteratedGraphDerivativeRelation_realize_iff_on_Ioo
    G p f a b N hrep hf n.val (Nat.lt_succ_iff.mp n.isLt) x hx
  constructor
  · rintro ⟨y,hy,hlo,hhi⟩
    have he := (hr (y ())).mp hy
    rw [he] at hlo hhi
    exact abs_lt.mpr ⟨hlo,hhi⟩
  · intro h
    exact ⟨fun _ => iteratedDeriv n.val f x,(hr _).mpr rfl,(abs_lt.mp h).1,(abs_lt.mp h).2⟩

theorem isOpen_strictDerivativeGoodSet {f : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ N f (Ioo a b)) (T : Fin (N+1) → ℝ) :
    IsOpen (strictDerivativeGoodSet f N a b T) := by
  have he : strictDerivativeGoodSet f N a b T =
      ⋂ n : Fin (N+1), {x | x ∈ Ioo a b ∧ |iteratedDeriv n.val f x| < T n} := by
    ext x
    simp only [strictDerivativeGoodSet,mem_setOf_eq,mem_iInter]
    constructor
    · rintro ⟨hx,h⟩ n; exact ⟨hx,h n⟩
    · intro h; exact ⟨(h 0).1,fun n => (h n).2⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro n
  exact (continuousOn_iteratedDeriv_of_contDiffOn_Ioo hf
    (Nat.lt_succ_iff.mp n.isLt)).abs.isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem published_uniform_strictDerivativeGoodSet_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) (N : ℕ) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ) (T : Fin (N+1) → ℝ),
      (∀ x ∈ Ioo a b, ∀ y : ℝ, Sum.elim p ![x,y] ∈ G ↔ y=f x) →
      ContDiffOn ℝ N f (Ioo a b) →
      Finite (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ∧
        Nat.card (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ≤ K := by
  obtain ⟨K,hK⟩ := published_projection_fiber_component_bound hCell hHardt hQE
    (derivativeGoodRelation G N)
    (hQE.finite_sign_description _ (derivativeGoodRelation_definable hG N))
  refine ⟨K,?_⟩
  intro p f a b T hrep hf
  have h := finite_connectedComponents_and_card_le_of_homeomorph
    (projectionFiberUnitHomeomorphScalar (derivativeGoodRelation G N)
      (Sum.elim p (Sum.elim ![a,b] T))) (hK _)
  have he : scalarProjectionFiber (derivativeGoodRelation G N)
      (Sum.elim p (Sum.elim ![a,b] T)) = strictDerivativeGoodSet f N a b T := by
    ext x
    exact derivativeGoodRelation_realize_iff G p f a b N T hrep hf x
  exact he ▸ h

theorem published_bounded_tuple_strictDerivativeGoodSet_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D N : ℕ) :
    ∃ K : ℕ, ∀ (P : Fin s → MvPolynomial (Fin 2) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin 2 → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S →
      ∀ (f : ℝ → ℝ) (a b : ℝ) (T : Fin (N+1) → ℝ),
      (∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x) →
      ContDiffOn ℝ N f (Ioo a b) →
      Finite (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ∧
        Nat.card (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ≤ K := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_uniform_strictDerivativeGoodSet_components hCell hHardt hQE
      (universalPolynomialBooleanSet (Fin 2) s D q)
      (hasPolynomialSignDescription_definable
        (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin 2) s D q)) N
  choose K hK using h
  refine ⟨Finset.univ.sup K,?_⟩
  intro P hP S hS f a b T hrep hf
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hS
  have hrep' : ∀ x ∈ Ioo a b, ∀ y : ℝ,
      Sum.elim (polynomialFamilyCoefficients D P) ![x,y] ∈
        universalPolynomialBooleanSet (Fin 2) s D q ↔ y=f x := by
    intro x hx y
    simpa only [hEq,mem_setOf_eq] using hrep x hx y
  have hb := hK q (polynomialFamilyCoefficients D P) f a b T hrep' hf
  exact ⟨hb.1,hb.2.trans (Finset.le_sup (f := K) (Finset.mem_univ q))⟩

theorem published_bounded_format_strictDerivativeGoodSet_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D N : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ)),
      A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A S →
      ∀ (f : ℝ → ℝ) (a b : ℝ) (T : Fin (N+1) → ℝ),
      (∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x) →
      ContDiffOn ℝ N f (Ioo a b) →
      Finite (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ∧
        Nat.card (ConnectedComponents (strictDerivativeGoodSet f N a b T)) ≤ K := by
  obtain ⟨K,hK⟩ := published_bounded_tuple_strictDerivativeGoodSet_components hCell hHardt hQE s D N
  refine ⟨K,?_⟩
  intro A S hc hd hS f a b T hrep hf
  obtain ⟨P,hP,hSP⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hc hd hS
  exact hK P hP S hSP f a b T hrep hf

end PaperI
