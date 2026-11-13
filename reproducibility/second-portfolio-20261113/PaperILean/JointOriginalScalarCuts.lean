import PaperILean.PublishedUniformAnalyticCuts
import PaperILean.DerivativeSignCutConstruction

/-! Retain the actual JOINT finite cut relation used by the original analytic
and derivative-sign construction. No definability of an analytic predicate,
measurability of arbitrary pointwise choices, or new external input is assumed. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def jointUnitCutRelation {α ι : Type*} (B : ι → Set ((α ⊕ Unit) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Icc (0 : ℝ) 1 ∧
    (v (Sum.inr ()) = 0 ∨ v (Sum.inr ()) = 1 ∨ ∃ i, v ∈ B i)}

theorem jointUnitCutRelation_definable {α ι : Type*} [Finite α] [Fintype ι]
    {B : ι → Set ((α ⊕ Unit) → ℝ)}
    (hB : ∀ i, (univ : Set ℝ).Definable Language.ring (B i)) :
    (univ : Set ℝ).Definable Language.ring (jointUnitCutRelation B) := by
  have h0 := realPolynomial_le_definable (0 : MvPolynomial (α ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inr ()))
  have h1 := realPolynomial_le_definable (MvPolynomial.X (Sum.inr () : α ⊕ Unit)) 1
  have hz := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr () : α ⊕ Unit))
  have ho := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr () : α ⊕ Unit) - 1)
  have he := (realDefinable_finite_all (fun i => (hB i).compl)).compl
  convert (h0.inter h1).inter (hz.union (ho.union he)) using 1
  ext v
  simp [jointUnitCutRelation, sub_eq_zero]

theorem jointUnitCutRelation_fiber {α ι : Type*}
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) (t : ℝ) :
    t ∈ scalarProjectionFiber (jointUnitCutRelation B) p ↔
      t ∈ Icc (0 : ℝ) 1 ∧ (t = 0 ∨ t = 1 ∨ ∃ i, t ∈ scalarProjectionFiber (B i) p) := Iff.rfl

theorem jointUnitCutRelation_endpoints {α ι : Type*}
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) :
    0 ∈ scalarProjectionFiber (jointUnitCutRelation B) p ∧
    1 ∈ scalarProjectionFiber (jointUnitCutRelation B) p := by
  constructor <;> rw [jointUnitCutRelation_fiber] <;> norm_num

theorem jointUnitCutRelation_subset {α ι : Type*}
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) :
    scalarProjectionFiber (jointUnitCutRelation B) p ⊆ Icc (0 : ℝ) 1 :=
  fun _ ht => ht.1

theorem jointUnitCutRelation_finite {α ι : Type*} [Finite ι]
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ)
    (hB : ∀ i, (scalarProjectionFiber (B i) p).Finite) :
    (scalarProjectionFiber (jointUnitCutRelation B) p).Finite := by
  have hf : ({0,1} ∪ ⋃ i, scalarProjectionFiber (B i) p : Set ℝ).Finite :=
    ((finite_singleton 1).insert 0).union (finite_iUnion hB)
  apply hf.subset
  intro t ht
  rcases (jointUnitCutRelation_fiber B p t).mp ht with ⟨_,h | h | ⟨i,hi⟩⟩
  · exact Or.inl (by simp [h])
  · exact Or.inl (by simp [h])
  · exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)

theorem jointUnitCutRelation_gap_avoids {α ι : Type*}
    (B : ι → Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) {u v : ℝ}
    (hu : u ∈ scalarProjectionFiber (jointUnitCutRelation B) p)
    (hv : v ∈ scalarProjectionFiber (jointUnitCutRelation B) p)
    (hgap : ∀ c ∈ scalarProjectionFiber (jointUnitCutRelation B) p, c ∉ Ioo u v) :
    ∀ i, ∀ x ∈ Ioo u v, x ∉ scalarProjectionFiber (B i) p := by
  intro i x hx hxi
  apply hgap x _ hx
  exact ⟨⟨hu.1.1.trans hx.1.le,hx.2.le.trans hv.1.2⟩,Or.inr (Or.inr ⟨i,hxi⟩)⟩

def JointOriginalScalarCutFamily {α : Type*}
    (G : Set ((α ⊕ Fin 2) → ℝ)) (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ) : Prop :=
  ∀ p : α → ℝ, (scalarProjectionFiber C p).Finite ∧
    Nat.card (scalarProjectionFiber C p) ≤ K ∧
    0 ∈ scalarProjectionFiber C p ∧ 1 ∈ scalarProjectionFiber C p ∧
    scalarProjectionFiber C p ⊆ Icc (0 : ℝ) 1 ∧
    ∀ f : ℝ → ℝ,
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ y, Sum.elim p ![t,y] ∈ G ↔ y = f t) →
      ∀ u ∈ scalarProjectionFiber C p, ∀ v ∈ scalarProjectionFiber C p,
        u < v → (∀ c ∈ scalarProjectionFiber C p, c ∉ Ioo u v) →
        AnalyticOnNhd ℝ f (Ioo u v) ∧ DerivativeSignOn f (Ioo u v)

/-- One fixed joint relation, not a family of arbitrary pointwise cut choices.
The finite budget precedes every parameter and every represented function.
Analytic pieces supply differentiability, so no separate nonsmooth-locus
choice is needed. Constant pieces and entire zero-derivative intervals remain. -/
theorem published_joint_original_scalar_cut_family
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ (C : Set ((α ⊕ Unit) → ℝ)) (K : ℕ),
      HasPolynomialSignDescription C ∧ JointOriginalScalarCutFamily G C K := by
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
  let C := jointUnitCutRelation B
  have hC : HasPolynomialSignDescription C :=
    hQE.finite_sign_description _ (jointUnitCutRelation_definable hB)
  obtain ⟨K,hK⟩ := published_scalar_finite_fiber_card_bound hCell hHardt hQE C hC
  refine ⟨C,K,hC,?_⟩
  intro p
  have hf := jointUnitCutRelation_finite B p (hBfin p)
  have he := jointUnitCutRelation_endpoints B p
  refine ⟨hf,hK p hf,he.1,he.2,jointUnitCutRelation_subset B p,?_⟩
  intro f hrep u hu v hv huv hgap
  have hAvoid := jointUnitCutRelation_gap_avoids B p hu hv hgap
  have hsub : Ioo u v ⊆ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨hu.1.1.trans_lt hx.1,hx.2.trans_le hv.1.2⟩
  have hA : AnalyticOnNhd ℝ f (Ioo u v) :=
    analyticOnNhd_of_unique_graph_piece_frontiers G V (fun i => (hV i).2.2)
      hCover p f 0 1 u v hrep (fun _ hx => ⟨(hsub hx).1.le,(hsub hx).2.le⟩)
      (fun i => hAvoid (Sum.inl i))
  refine ⟨hA,derivativeSignOn_of_graph_frontier_avoidance G p f 0 1 u v hrep hsub
    (fun x hx => (hA x hx).differentiableAt) ?_ ?_ ?_⟩
  · exact hAvoid (Sum.inr 0)
  · exact hAvoid (Sum.inr 1)
  · exact hAvoid (Sum.inr 2)

end PaperI
