import PaperILean.JointOriginalScalarCuts
import PaperILean.RegularCenterlineInterval

/-! Original regular subdivision with BOTH interval endpoints retained as
parameters. The cut relation consists of actual piece/sign frontiers and the
endpoints, never an assumed definable analytic-locus predicate. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointIntervalCutRelation {α ι : Type*} (B : ι → Set ((α ⊕ Unit) → ℝ)) :
    Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Icc (v (Sum.inl (Sum.inr 0))) (v (Sum.inl (Sum.inr 1))) ∧
    (v (Sum.inr ()) = v (Sum.inl (Sum.inr 0)) ∨
      v (Sum.inr ()) = v (Sum.inl (Sum.inr 1)) ∨
      ∃ i, Sum.elim (fun c => v (Sum.inl (Sum.inl c))) (fun _ => v (Sum.inr ())) ∈ B i)}

theorem jointIntervalCutRelation_definable {α ι : Type*} [Finite α] [Fintype ι]
    {B : ι → Set ((α ⊕ Unit) → ℝ)}
    (hB : ∀ i, (univ : Set ℝ).Definable Language.ring (B i)) :
    (univ : Set ℝ).Definable Language.ring (jointIntervalCutRelation B) := by
  let e : α ⊕ Unit → (α ⊕ Fin 2) ⊕ Unit :=
    Sum.elim (fun c => Sum.inl (Sum.inl c)) Sum.inr
  have he := (realDefinable_finite_all (fun i => ((hB i).preimage_comp e).compl)).compl
  have ha := realPolynomial_le_definable (MvPolynomial.X (Sum.inl (Sum.inr 0) : (α ⊕ Fin 2) ⊕ Unit)) (MvPolynomial.X (Sum.inr ()))
  have hb := realPolynomial_le_definable (MvPolynomial.X (Sum.inr () : (α ⊕ Fin 2) ⊕ Unit)) (MvPolynomial.X (Sum.inl (Sum.inr 1)))
  have h0 := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr () : (α ⊕ Fin 2) ⊕ Unit) - MvPolynomial.X (Sum.inl (Sum.inr 0)))
  have h1 := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr () : (α ⊕ Fin 2) ⊕ Unit) - MvPolynomial.X (Sum.inl (Sum.inr 1)))
  convert (ha.inter hb).inter (h0.union (h1.union he)) using 1
  ext v
  have hv : v ∘ e = Sum.elim (fun c => v (Sum.inl (Sum.inl c))) (fun _ => v (Sum.inr ())) := by
    funext z; cases z <;> rfl
  simp [jointIntervalCutRelation, hv, sub_eq_zero]

theorem jointIntervalCutRelation_fiber {α ι : Type*}
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) (a b x : ℝ) :
    x ∈ scalarProjectionFiber (jointIntervalCutRelation B) (Sum.elim p ![a,b]) ↔
      x ∈ Icc a b ∧ (x=a ∨ x=b ∨ ∃ i, x ∈ scalarProjectionFiber (B i) p) := Iff.rfl

theorem jointIntervalCutRelation_finite {α ι : Type*} [Finite ι]
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) (a b : ℝ)
    (hB : ∀ i, (scalarProjectionFiber (B i) p).Finite) :
    (scalarProjectionFiber (jointIntervalCutRelation B) (Sum.elim p ![a,b])).Finite := by
  apply (((finite_singleton b).insert a).union (finite_iUnion hB)).subset
  intro x hx
  rcases (jointIntervalCutRelation_fiber B p a b x).mp hx with ⟨_,h | h | ⟨i,hi⟩⟩
  · exact Or.inl (by simp [h])
  · exact Or.inl (by simp [h])
  · exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)

def JointOriginalIntervalCutFamily {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (C : Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ)) (K : ℕ) : Prop :=
  ∀ (p : α → ℝ) (a b : ℝ), a ≤ b →
    (scalarProjectionFiber C (Sum.elim p ![a,b])).Finite ∧
    Nat.card (scalarProjectionFiber C (Sum.elim p ![a,b])) ≤ K ∧
    a ∈ scalarProjectionFiber C (Sum.elim p ![a,b]) ∧
    b ∈ scalarProjectionFiber C (Sum.elim p ![a,b]) ∧
    scalarProjectionFiber C (Sum.elim p ![a,b]) ⊆ Icc a b ∧
    ∀ f : ℝ → ℝ,
      (∀ x ∈ Icc a b, ∀ y, Sum.elim p ![x,y] ∈ G ↔ y=f x) →
      ∀ u ∈ scalarProjectionFiber C (Sum.elim p ![a,b]),
      ∀ v ∈ scalarProjectionFiber C (Sum.elim p ![a,b]), u<v →
      (∀ c ∈ scalarProjectionFiber C (Sum.elim p ![a,b]), c ∉ Ioo u v) →
      AnalyticOnNhd ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v)

/-- The bound is chosen before every coefficient, interval and represented
function. Singleton intervals remain in this cut-family statement. -/
theorem published_joint_original_interval_cut_family
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ (C : Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ)) (K : ℕ),
      HasPolynomialSignDescription C ∧ JointOriginalIntervalCutFamily G C K := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨n,V,hV,hCover⟩ := published_unique_graph_finite_analytic_pieces hPiece hQE G hG
  let S : Fin 3 → Set ((α ⊕ Unit) → ℝ) :=
    ![graphPositiveDerivativeRelation G,graphZeroDerivativeRelation G,graphNegativeDerivativeRelation G]
  have hS (i : Fin 3) : (univ : Set ℝ).Definable Language.ring (S i) := by
    fin_cases i
    · exact graphPositiveDerivativeRelation_definable hG
    · exact graphZeroDerivativeRelation_definable hG
    · exact graphNegativeDerivativeRelation_definable hG
  let B : (Fin n ⊕ Fin 3) → Set ((α ⊕ Unit) → ℝ) :=
    Sum.elim (fun i => scalarFrontierRelation (V i)) (fun i => scalarFrontierRelation (S i))
  have hB (i : Fin n ⊕ Fin 3) : (univ : Set ℝ).Definable Language.ring (B i) := by
    cases i with
    | inl i => exact scalarFrontierRelation_definable (hasPolynomialSignDescription_definable (hV i).1)
    | inr i => exact scalarFrontierRelation_definable (hS i)
  have hBfin (p : α → ℝ) (i : Fin n ⊕ Fin 3) : (scalarProjectionFiber (B i) p).Finite := by
    cases i with
    | inl i => exact published_scalar_fiber_frontier_finite hCell (V i) (hV i).1 p
    | inr i => exact published_scalar_fiber_frontier_finite hCell (S i) (hQE.finite_sign_description _ (hS i)) p
  let C := jointIntervalCutRelation B
  have hC : HasPolynomialSignDescription C := hQE.finite_sign_description _ (jointIntervalCutRelation_definable hB)
  obtain ⟨K,hK⟩ := published_scalar_finite_fiber_card_bound hCell hHardt hQE C hC
  refine ⟨C,K,hC,?_⟩
  intro p a b hab
  have hf := jointIntervalCutRelation_finite B p a b (hBfin p)
  have ha : a ∈ scalarProjectionFiber C (Sum.elim p ![a,b]) := ⟨⟨le_rfl,hab⟩,Or.inl rfl⟩
  have hb : b ∈ scalarProjectionFiber C (Sum.elim p ![a,b]) := ⟨⟨hab,le_rfl⟩,Or.inr (Or.inl rfl)⟩
  have hsub : scalarProjectionFiber C (Sum.elim p ![a,b]) ⊆ Icc a b := fun _ hx => hx.1
  refine ⟨hf,hK _ hf,ha,hb,hsub,?_⟩
  intro f hrep u hu v hv huv hgap
  have hinside : Ioo u v ⊆ Ioo a b := fun _ hx => ⟨(hsub hu).1.trans_lt hx.1,hx.2.trans_le (hsub hv).2⟩
  have hAvoid (i) (x : ℝ) (hx : x∈Ioo u v) : x∉scalarProjectionFiber (B i) p := by
    intro hxi
    exact hgap x ⟨⟨(hinside hx).1.le,(hinside hx).2.le⟩,Or.inr (Or.inr ⟨i,hxi⟩)⟩ hx
  have hA : AnalyticOnNhd ℝ f (Ioo u v) :=
    analyticOnNhd_of_unique_graph_piece_frontiers G V (fun i => (hV i).2.2) hCover
      p f a b u v hrep (fun _ hx => ⟨(hinside hx).1.le,(hinside hx).2.le⟩)
      (fun i => hAvoid (Sum.inl i))
  refine ⟨hA,derivativeSignOn_of_graph_frontier_avoidance G p f a b u v hrep hinside
    (fun x hx => (hA x hx).differentiableAt) ?_ ?_ ?_⟩
  · exact hAvoid (Sum.inr 0)
  · exact hAvoid (Sum.inr 1)
  · exact hAvoid (Sum.inr 2)

end PaperI
