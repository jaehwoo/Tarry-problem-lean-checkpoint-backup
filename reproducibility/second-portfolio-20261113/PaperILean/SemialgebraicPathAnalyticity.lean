import PaperILean.SemialgebraicPathData
import PaperILean.PublishedScalarAnalyticity
import PaperILean.PublishedRealAlgebraicAssumptions

/-! The coordinate projection of an actual path graph uses one common vector
witness. Accepted one-dimensional Nash regularity then gives actual finite
analytic pieces of that path, without changing the path or its graph format. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem unitPath_open_coordinate_graph_definable {κ : Type*} [Finite κ]
    (γ : ℝ → κ → ℝ) (hγ : HasPolynomialSignDescription (unitPathGraph γ)) (k : κ) :
    (univ : Set ℝ).Definable Language.ring
      (openScalarGraph (fun t => γ t k) 0 1) := by
  let e : Unit ⊕ κ → Fin 2 ⊕ κ := Sum.elim (fun _ => Sum.inl 0) Sum.inr
  have hEq := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inr k : Fin 2 ⊕ κ) - MvPolynomial.X (Sum.inl 1))
  have hProj := realDefinable_exists
    (((hasPolynomialSignDescription_definable hγ).preimage_comp e).inter hEq)
  have h0 := (realPolynomial_le_definable (MvPolynomial.X (0 : Fin 2)) 0).compl
  have h1 := (realPolynomial_le_definable (1 : MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X 0)).compl
  convert hProj.inter (h0.inter h1) using 1
  ext v
  have he (w : κ → ℝ) : (Sum.elim v w ∘ e) = Sum.elim (fun _ => v 0) w := by
    funext i
    rcases i with i | i <;> rfl
  simp only [openScalarGraph, mem_setOf_eq, mem_inter_iff, mem_preimage,
    mem_compl_iff, map_sub, MvPolynomial.eval_X, map_zero, map_one, sub_eq_zero,
    not_le, Sum.elim_inl, Sum.elim_inr, he]
  change (0 < v 0 ∧ v 0 < 1 ∧ v 1 = γ (v 0) k) ↔
    ((∃ w : κ → ℝ, (Sum.elim (fun _ => v 0) w ∈ unitPathGraph γ) ∧ w k = v 1) ∧
      0 < v 0 ∧ v 0 < 1)
  simp only [unitPathGraph_mem_iff]
  constructor
  · rintro ⟨h0,h1,hy⟩
    exact ⟨⟨γ (v 0),⟨⟨h0.le,h1.le⟩,rfl⟩,hy.symm⟩,h0,h1⟩
  · rintro ⟨⟨w,⟨_,hw⟩,hy⟩,h0,h1⟩
    exact ⟨h0,h1,hy.symm.trans (congrFun hw k)⟩

theorem published_unitPath_open_coordinate_graph_sign_description
    (hQE : PublishedRealSemialgebraicity) {κ : Type} [Finite κ]
    (γ : ℝ → κ → ℝ) (hγ : HasPolynomialSignDescription (unitPathGraph γ)) (k : κ) :
    HasPolynomialSignDescription (openScalarGraph (fun t => γ t k) 0 1) :=
  hQE.finite_sign_description _ (unitPath_open_coordinate_graph_definable γ hγ k)

theorem SemialgebraicUnitPath.published_finite_analytic_exceptions
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {κ : Type} [Fintype κ] {S : Set (κ → ℝ)} {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath S a b) :
    ∃ C : Finset ℝ, (∀ c ∈ C, c ∈ Ioo (0 : ℝ) 1) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ C → AnalyticAt ℝ γ.toFun t := by
  apply published_finite_pi_analytic_exceptions hNash γ.toFun 0 1 zero_lt_one
  exact published_unitPath_open_coordinate_graph_sign_description hQE γ.toFun γ.semialgebraic

/-- The same original path is analytic on finitely many open subintervals. Its
continuous endpoints and its existing graph-format bound are unchanged. -/
theorem SemialgebraicUnitPath.published_finite_analytic_cut_intervals
    (hQE : PublishedRealSemialgebraicity) (hNash : PublishedOneVariableNashRegularity)
    {κ : Type} [Fintype κ] {S : Set (κ → ℝ)} {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath S a b) :
    ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0 : ℝ) 1) ∧
      ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
        AnalyticOnNhd ℝ γ.toFun (Ioo u v) := by
  apply published_finite_pi_analytic_cut_intervals hNash γ.toFun 0 1 zero_lt_one
  exact published_unitPath_open_coordinate_graph_sign_description hQE γ.toFun γ.semialgebraic

end PaperI
