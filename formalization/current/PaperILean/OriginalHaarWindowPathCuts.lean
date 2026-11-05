import PaperILean.CompatibleHardtForMonotonicity
import PaperILean.CoordinatePathFormat
import PaperILean.PublishedScalarCompositionFormat
import PaperILean.PublishedOriginalScalarSubdivision

/-! Actual polynomial orbit coordinates along the chosen bounded-format path
have uniformly many common analytic/sign pieces. No bound on the absolute
group coordinates or on the entire component is required. -/
noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def originalHaarPolynomialGraphAtom {κ : Type*} (q : MvPolynomial κ ℝ) :
    MvPolynomial (κ ⊕ Unit) ℝ :=
  MvPolynomial.X (Sum.inr ())-MvPolynomial.rename Sum.inl q

theorem originalHaar_polynomial_graph_format {κ : Type*}
    (A : Finset (MvPolynomial κ ℝ)) (S : Set (κ → ℝ)) (s D E : ℕ)
    (hcard : A.card ≤ s) (hdeg : ∀ q ∈ A, q.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (q : MvPolynomial κ ℝ)
    (hq : q.totalDegree ≤ E) :
    ∃ B : Finset (MvPolynomial (κ ⊕ Unit) ℝ), B.card ≤ s+1 ∧
      (∀ p ∈ B, p.totalDegree ≤ max D (max E 1)) ∧
      PolynomialSignDetermined B (scalarFunctionGraph S (fun x => MvPolynomial.eval x q)) := by
  classical
  let B := A.image (MvPolynomial.rename Sum.inl) ∪ {originalHaarPolynomialGraphAtom q}
  refine ⟨B,?_,?_,?_⟩
  · exact (Finset.card_union_le _ _).trans (by
      simpa using Nat.add_le_add_right (Finset.card_image_le.trans hcard) 1)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
      exact (MvPolynomial.totalDegree_rename_le _ _).trans
        ((hdeg r hr).trans (Nat.le_max_left _ _))
    · rw [Finset.mem_singleton.mp hp]
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · exact (by simp : (MvPolynomial.X (Sum.inr () : κ ⊕ Unit) : MvPolynomial _ ℝ).totalDegree ≤ 1).trans
          ((Nat.le_max_right E 1).trans (Nat.le_max_right D (max E 1)))
      · exact (MvPolynomial.totalDegree_rename_le _ _).trans
          (hq.trans ((Nat.le_max_left E 1).trans (Nat.le_max_right D (max E 1))))
  · intro x y hxy
    have hdom : (fun k => x (Sum.inl k)) ∈ S ↔ (fun k => y (Sum.inl k)) ∈ S := by
      apply hS
      intro p hp
      simpa only [MvPolynomial.eval_rename,Function.comp_def] using
        hxy (MvPolynomial.rename Sum.inl p)
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
    have he := (hxy (originalHaarPolynomialGraphAtom q)
      (Finset.mem_union_right _ (Finset.mem_singleton_self _))).1
    simp only [originalHaarPolynomialGraphAtom,map_sub,MvPolynomial.eval_X,
      MvPolynomial.eval_rename,Function.comp_def,sub_eq_zero] at he
    exact and_congr hdom he

/-- A single common analytic/sign cut set includes every polynomial readout
of the actual path. The bound precedes all coefficients and endpoints.
Group coordinates can be included as degree-one readouts even when their
range on the entire component is unbounded. -/
theorem published_originalHaar_polynomial_path_cuts
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions)
    (κ ι : Type) [Fintype κ] [Fintype ι] (sS dS sPath dPath E : ℕ) :
    ∃ K : ℕ, ∀ (S : Set (κ → ℝ)) (A : Finset (MvPolynomial κ ℝ)),
      A.card ≤ sS → (∀ q ∈ A, q.totalDegree ≤ dS) → PolynomialSignDetermined A S →
      ∀ (a b : κ → ℝ) (γ : SemialgebraicUnitPath S a b)
        (P : Finset (MvPolynomial (Unit ⊕ κ) ℝ)),
      P.card ≤ sPath → (∀ q ∈ P, q.totalDegree ≤ dPath) →
      PolynomialSignDetermined P (unitPathGraph γ.toFun) →
      ∀ Q : ι → MvPolynomial κ ℝ, (∀ i, (Q i).totalDegree ≤ E) →
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0:ℝ) 1) ∧
        C.card ≤ K ∧
        ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          ∀ i, AnalyticOnNhd ℝ (fun t => MvPolynomial.eval (γ.toFun t) (Q i)) (Ioo u v) ∧
            DerivativeSignOn (fun t => MvPolynomial.eval (γ.toFun t) (Q i)) (Ioo u v) := by
  obtain ⟨sOut,dOut,hFormat⟩ := published_bounded_scalar_composition_sign_format
    hQE κ sPath dPath (sS+1) (max dS (max E 1))
  obtain ⟨K,hK⟩ := published_bounded_sign_format_original_common_subdivision
    hCell hHardt.toHardtTriviality hQE hNash hPiece ι sOut dOut
  refine ⟨K,?_⟩
  intro S A hAc hAd hAS a b γ P hPc hPd hPS Q hQ
  apply hK (fun i t => MvPolynomial.eval (γ.toFun t) (Q i)) 0 1 (by norm_num)
  · intro i
    exact γ.comp_continuousOn _ (Q i).continuous_eval.continuousOn
  · intro i
    obtain ⟨AF,hAFc,hAFd,hAF⟩ := originalHaar_polynomial_graph_format
      A S sS dS E hAc hAd hAS (Q i) (hQ i)
    obtain ⟨B,hBc,hBd,hB⟩ := hFormat P AF (unitPathGraph γ.toFun)
      (scalarFunctionGraph S (fun x => MvPolynomial.eval x (Q i)))
      hPc hPd hPS hAFc hAFd hAF
    exact ⟨B,scalarRelationComposition (unitPathGraph γ.toFun)
      (scalarFunctionGraph S (fun x => MvPolynomial.eval x (Q i))),
      hBc,hBd,hB,scalarRelationComposition_unitPathGraph γ _⟩

end PaperI
