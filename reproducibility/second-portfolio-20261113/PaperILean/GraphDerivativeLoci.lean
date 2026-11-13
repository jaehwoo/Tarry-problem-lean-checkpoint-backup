import PaperILean.GraphDerivativeDefinability

/-! Actual derivative-existence and signed-derivative loci. The derivative
must exist even in the zero-sign case; Lean's default value of `deriv` at a
nondifferentiable point is not used to certify a zero derivative. The local
realization requires graph correctness only on the original closed interval.
Pre-strategy diagnostics: checkpoint_108_derivative_sign_pre_strategy.json. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def graphDerivativeLocus {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) (T : Set ℝ) :
    Set ((α ⊕ Unit) → ℝ) :=
  {v | ∃ m : Unit → ℝ,
    Sum.elim (v ∘ Sum.inl) ![v (Sum.inr ()),m ()] ∈ graphDerivativeRelation G ∧ m () ∈ T}

def graphDerivativeExistsRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) := graphDerivativeLocus G univ

def graphPositiveDerivativeRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) := graphDerivativeLocus G (Ioi 0)

def graphZeroDerivativeRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) := graphDerivativeLocus G {0}

def graphNegativeDerivativeRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) := graphDerivativeLocus G (Iio 0)

theorem graphDerivativeLocus_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} {T : Set ℝ}
    (hG : (univ : Set ℝ).Definable Language.ring G)
    (hT : (univ : Set ℝ).Definable Language.ring {m : Unit → ℝ | m () ∈ T}) :
    (univ : Set ℝ).Definable Language.ring (graphDerivativeLocus G T) := by
  let e : (α ⊕ Fin 2) → (α ⊕ Unit) ⊕ Unit := Sum.elim
    (fun a => Sum.inl (Sum.inl a))
    (fun i => if i = 0 then Sum.inl (Sum.inr ()) else Sum.inr ())
  have h := realDefinable_exists (((graphDerivativeRelation_definable hG).preimage_comp e).inter
    (hT.preimage_comp Sum.inr))
  convert h using 1

theorem graphDerivativeExistsRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphDerivativeExistsRelation G) := by
  apply graphDerivativeLocus_definable hG
  simpa using (Set.definable_univ : (univ : Set ℝ).Definable Language.ring (univ : Set (Unit → ℝ)))

theorem graphPositiveDerivativeRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphPositiveDerivativeRelation G) := by
  apply graphDerivativeLocus_definable hG
  simpa only [mem_Ioi, map_zero, MvPolynomial.eval_X] using
    realPolynomial_lt_definable (0 : MvPolynomial Unit ℝ) (MvPolynomial.X ())

theorem graphZeroDerivativeRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphZeroDerivativeRelation G) := by
  apply graphDerivativeLocus_definable hG
  simpa only [mem_singleton_iff, MvPolynomial.eval_X] using
    realPolynomial_zero_definable (MvPolynomial.X (() : Unit))

theorem graphNegativeDerivativeRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphNegativeDerivativeRelation G) := by
  apply graphDerivativeLocus_definable hG
  simpa only [mem_Iio, map_zero, MvPolynomial.eval_X] using
    realPolynomial_lt_definable (MvPolynomial.X (() : Unit)) 0

theorem graphDerivativeLocus_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (T : Set ℝ) (p : α → ℝ) (f : ℝ → ℝ)
    (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p (fun _ => x) ∈ graphDerivativeLocus G T ↔
      DifferentiableAt ℝ f x ∧ deriv f x ∈ T := by
  constructor
  · rintro ⟨m,hm,hmT⟩
    have hd := (graphDerivativeRelation_realize_iff_on_interval G p f a b x (m ()) hG hx).mp hm
    exact ⟨hd.differentiableAt, by simpa only [hd.deriv] using hmT⟩
  · rintro ⟨hd,hdT⟩
    exact ⟨fun _ => deriv f x,
      (graphDerivativeRelation_realize_iff_on_interval G p f a b x (deriv f x) hG hx).mpr hd.hasDerivAt,
      hdT⟩

theorem graphDerivativeExistsRelation_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p (fun _ => x) ∈ graphDerivativeExistsRelation G ↔ DifferentiableAt ℝ f x := by
  simpa only [graphDerivativeExistsRelation, mem_univ, and_true] using
    graphDerivativeLocus_realize_iff_on_interval G univ p f a b x hG hx

theorem graphPositiveDerivativeRelation_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p (fun _ => x) ∈ graphPositiveDerivativeRelation G ↔
      DifferentiableAt ℝ f x ∧ 0 < deriv f x := by
  exact graphDerivativeLocus_realize_iff_on_interval G (Ioi 0) p f a b x hG hx

theorem graphZeroDerivativeRelation_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p (fun _ => x) ∈ graphZeroDerivativeRelation G ↔
      DifferentiableAt ℝ f x ∧ deriv f x = 0 := by
  exact graphDerivativeLocus_realize_iff_on_interval G {0} p f a b x hG hx

theorem graphNegativeDerivativeRelation_realize_iff_on_interval {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t)
    (hx : x ∈ Ioo a b) :
    Sum.elim p (fun _ => x) ∈ graphNegativeDerivativeRelation G ↔
      DifferentiableAt ℝ f x ∧ deriv f x < 0 := by
  exact graphDerivativeLocus_realize_iff_on_interval G (Iio 0) p f a b x hG hx

def nondifferentiabilitySet (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ¬ DifferentiableAt ℝ f x}

def graphNondifferentiabilityRelation {α : Type*} (G : Set ((α ⊕ Fin 2) → ℝ)) :
    Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr 0))) (v (Sum.inl (Sum.inr 1))) ∧
    Sum.elim (fun a => v (Sum.inl (Sum.inl a))) (fun _ => v (Sum.inr ())) ∉
      graphDerivativeExistsRelation G}

theorem graphNondifferentiabilityRelation_definable {α : Type*} [Finite α]
    {G : Set ((α ⊕ Fin 2) → ℝ)} (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (graphNondifferentiabilityRelation G) := by
  let e : α ⊕ Unit → (α ⊕ Fin 2) ⊕ Unit :=
    Sum.elim (fun a => Sum.inl (Sum.inl a)) Sum.inr
  have h := ((realCoordinate_lt_definable (Sum.inl (Sum.inr 0)) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr 1)))).inter
      ((graphDerivativeExistsRelation_definable hG).preimage_comp e).compl
  convert h using 1

theorem graphNondifferentiabilityRelation_realize_iff {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (f : ℝ → ℝ) (a b x : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ y : ℝ, Sum.elim p ![t,y] ∈ G ↔ y = f t) :
    Sum.elim (Sum.elim p ![a,b]) (fun _ => x) ∈ graphNondifferentiabilityRelation G ↔
      x ∈ nondifferentiabilitySet f a b := by
  change (x ∈ Ioo a b ∧ ¬ _) ↔ (x ∈ Ioo a b ∧ ¬ _)
  apply and_congr_right
  intro hx
  exact not_congr (graphDerivativeExistsRelation_realize_iff_on_interval G p f a b x hG hx)

end PaperI
