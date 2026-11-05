import PaperILean.RegularSectionDifferential
import PaperILean.OriginalHaarOrbitPolynomial
import PaperILean.OriginalHaarWindowPathCuts

/-! Actual full augmented polynomial readouts and common analytic/sign cuts for
I3244[45,140). The common bound precedes the seed, path, coefficients and all
endpoints. Physical affine constants are retained; no group-coordinate bound
or continuity at an excluded source endpoint is assumed. -/

noncomputable section
namespace PaperI.SectionIntegralReadouts
open Set Matrix
open MvPolynomial
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

abbrev ReadoutIndex (k : ℕ) := Fin 6 ⊕ AugmentedCoordinateIndex k

/-- Full physical translation, including its constant term. -/
def physicalTranslationPolynomial (ell : PhysicalAffineData) (i : Fin 3) :
    MvPolynomial (Fin 6) ℝ :=
  C (ell.1 i) + C (ell.2 i 0) * X 2 + C (ell.2 i 1) * X 4 + C (ell.2 i 2) * X 5

/-- Every entry of the composed physical linear matrix is retained. -/
def physicalMatrixPolynomial (ell : PhysicalAffineData) (i j : Fin 3) :
    MvPolynomial (Fin 6) ℝ :=
  ![C (ell.2 i 0), C (ell.2 i 0) * X 0 + C (ell.2 i 1),
    C (ell.2 i 0) * X 1 + C (ell.2 i 1) * X 3 + C (ell.2 i 2)] j

private theorem degree_const (r : ℝ) :
    (C r : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := by simp

private theorem degree_linear (r : ℝ) (i : Fin 6) :
    (C r * X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := by
  simpa using totalDegree_mul (C r : MvPolynomial (Fin 6) ℝ) (X i)

private theorem degree_add {p q : MvPolynomial (Fin 6) ℝ}
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    (p + q).totalDegree ≤ 1 := (totalDegree_add p q).trans (max_le hp hq)

private theorem physicalTranslationPolynomial_degree (ell : PhysicalAffineData) (i : Fin 3) :
    (physicalTranslationPolynomial ell i).totalDegree ≤ 1 :=
  degree_add (degree_add (degree_add (degree_const _) (degree_linear _ _))
    (degree_linear _ _)) (degree_linear _ _)

private theorem physicalMatrixPolynomial_degree (ell : PhysicalAffineData) (i j : Fin 3) :
    (physicalMatrixPolynomial ell i j).totalDegree ≤ 1 := by
  fin_cases j
  · exact degree_const _
  · exact degree_add (degree_linear _ _) (degree_const _)
  · exact degree_add (degree_add (degree_linear _ _) (degree_linear _ _)) (degree_const _)

private theorem physicalTranslationPolynomial_eval (ell : PhysicalAffineData)
    (x : Fin 6 → ℝ) (i : Fin 3) :
    eval x (physicalTranslationPolynomial ell i) =
      (RegularSectionDifferential.physicalPullback ell x).1 i := by
  simp [physicalTranslationPolynomial, RegularSectionDifferential.physicalPullback,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem physicalMatrixPolynomial_eval (ell : PhysicalAffineData)
    (x : Fin 6 → ℝ) (i j : Fin 3) :
    eval x (physicalMatrixPolynomial ell i j) =
      (RegularSectionDifferential.physicalPullback ell x).2 i j := by
  fin_cases j <;>
    simp [physicalMatrixPolynomial, RegularSectionDifferential.physicalPullback,
      originalUpperLinearMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The phase quotient removes only its own zeroth coefficient. The twelve
physical affine entries, including all constants, remain actual coordinates. -/
def augmentedPolynomial {k : ℕ} (S0 : AugmentedState k) :
    AugmentedCoordinateIndex k → MvPolynomial (Fin 6) ℝ :=
  Sum.elim (OriginalHaarOrbitPolynomial.orbitPolynomial S0.1)
    (Sum.elim (physicalTranslationPolynomial S0.2)
      (fun ij => physicalMatrixPolynomial S0.2 ij.1 ij.2))

theorem augmentedPolynomial_eval {k : ℕ} (S0 : AugmentedState k)
    (x : Fin 6 → ℝ) (i : AugmentedCoordinateIndex k) :
    eval x (augmentedPolynomial S0 i) =
      augmentedStateCoordinates k (RegularSectionDifferential.augmentedPullback S0 x) i := by
  rcases i with α | (i | ij)
  · exact OriginalHaarOrbitPolynomial.orbitPolynomial_eval S0.1 x α
  · exact physicalTranslationPolynomial_eval S0.2 x i
  · exact physicalMatrixPolynomial_eval S0.2 x ij.1 ij.2

theorem augmentedPolynomial_degree {k : ℕ} (S0 : AugmentedState k)
    (i : AugmentedCoordinateIndex k) :
    (augmentedPolynomial S0 i).totalDegree ≤ max k 1 := by
  rcases i with α | (i | ij)
  · exact (OriginalHaarOrbitPolynomial.orbitPolynomial_degree S0.1 α).trans
      (Nat.le_max_left _ _)
  · exact (physicalTranslationPolynomial_degree S0.2 i).trans (Nat.le_max_right _ _)
  · exact (physicalMatrixPolynomial_degree S0.2 ij.1 ij.2).trans (Nat.le_max_right _ _)

/-- Six original group coordinates are included so the actual path is analytic
on each gap even if its augmented seed is singular or zero. -/
def jointReadout {k : ℕ} (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ) :
    ReadoutIndex k → ℝ → ℝ :=
  Sum.elim (fun i t => g t i)
    (fun i t => augmentedStateCoordinates k
      (RegularSectionDifferential.augmentedPullback S0 (g t)) i)

def jointPolynomial {k : ℕ} (S0 : AugmentedState k) :
    ReadoutIndex k → MvPolynomial (Fin 6) ℝ :=
  Sum.elim X (augmentedPolynomial S0)

theorem jointPolynomial_eval {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (i : ReadoutIndex k) (t : ℝ) :
    eval (g t) (jointPolynomial S0 i) = jointReadout S0 g i t := by
  rcases i with i | i
  · exact eval_X _
  · exact augmentedPolynomial_eval S0 (g t) i

theorem jointPolynomial_degree {k : ℕ} (S0 : AugmentedState k) (i : ReadoutIndex k) :
    (jointPolynomial S0 i).totalDegree ≤ max k 1 := by
  rcases i with i | i
  · exact (by simp : (X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1).trans
      (Nat.le_max_right _ _)
  · exact augmentedPolynomial_degree S0 i

theorem jointReadout_continuousOn {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (S : Set ℝ) (hg : ContinuousOn g S) (i : ReadoutIndex k) :
    ContinuousOn (jointReadout S0 g i) S := by
  have h := (jointPolynomial S0 i).continuous_eval.comp_continuousOn hg
  simpa only [Function.comp_def, jointPolynomial_eval] using h

private theorem composition_graph {g : ℝ → Fin 6 → ℝ}
    {Γ : Set ((Unit ⊕ Fin 6) → ℝ)} {a z : ℝ}
    (hgraph : ∀ t ∈ Ioo a z, ∀ x : Fin 6 → ℝ,
      Sum.elim (fun _ : Unit => t) x ∈ Γ ↔ x = g t)
    (q : MvPolynomial (Fin 6) ℝ) (t : ℝ) (ht : t ∈ Ioo a z) (y : ℝ) :
    ![t,y] ∈ scalarRelationComposition Γ
      (scalarFunctionGraph Set.univ (fun x => eval x q)) ↔ y = eval (g t) q := by
  rw [scalarRelationComposition_mem]
  simp only [hgraph t ht, scalarFunctionGraph_mem, Set.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl, hy⟩
    exact hy
  · intro hy
    exact ⟨g t, rfl, hy⟩

/-- The same cut bound works for every interior compact interval, with no
extension of the actual graph to the excluded endpoints. Its quantifier
precedes all seeds, paths, graph atoms, coefficients and endpoints. -/
theorem actual_section_common_subdivision
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ K : ℕ, ∀ (S0 : AugmentedState k) (g : ℝ → Fin 6 → ℝ)
      (Γ : Set ((Unit ⊕ Fin 6) → ℝ)) (AΓ : Finset (MvPolynomial (Unit ⊕ Fin 6) ℝ))
      (a z : ℝ),
      AΓ.card ≤ s → (∀ p ∈ AΓ, p.totalDegree ≤ D) → PolynomialSignDetermined AΓ Γ →
      ContinuousOn g (Ioo a z) →
      (∀ t ∈ Ioo a z, ∀ x : Fin 6 → ℝ,
        Sum.elim (fun _ : Unit => t) x ∈ Γ ↔ x = g t) →
      ∀ u v : ℝ, u ≤ v → Icc u v ⊆ Ioo a z →
      ∃ C : Finset ℝ, u ∈ C ∧ v ∈ C ∧ (∀ c ∈ C, c ∈ Icc u v) ∧ C.card ≤ K ∧
        ∀ l ∈ C, ∀ r ∈ C, l < r → (∀ c ∈ C, c ∉ Ioo l r) →
          ∀ i, AnalyticOnNhd ℝ (jointReadout S0 g i) (Ioo l r) ∧
            DerivativeSignOn (jointReadout S0 g i) (Ioo l r) := by
  obtain ⟨sOut, DOut, hFormat⟩ := published_bounded_scalar_composition_sign_format
    hQE (Fin 6) s D 1 (max k 1)
  obtain ⟨K, hK⟩ := published_bounded_sign_format_original_common_subdivision
    hCell hHardt hQE hNash hPiece (ReadoutIndex k) sOut DOut
  refine ⟨K, ?_⟩
  intro S0 g Γ AΓ a z hcard hdegree hΓ hg hgraph u v huv hinside
  apply hK (jointReadout S0 g) u v huv
  · intro i
    exact (jointReadout_continuousOn S0 g (Ioo a z) hg i).mono hinside
  · intro i
    have hUniv : PolynomialSignDetermined (∅ : Finset (MvPolynomial (Fin 6) ℝ))
        (Set.univ : Set (Fin 6 → ℝ)) := by
      intro x y hxy
      exact iff_of_true (Set.mem_univ _) (Set.mem_univ _)
    obtain ⟨AF, hAFc, hAFd, hAF⟩ := originalHaar_polynomial_graph_format
      ∅ Set.univ 0 0 (max k 1) (by simp) (by simp) hUniv
      (jointPolynomial S0 i) (jointPolynomial_degree S0 i)
    have hAFc' : AF.card ≤ 1 := by simpa using hAFc
    have hAFd' : ∀ p ∈ AF, p.totalDegree ≤ max k 1 := by
      simpa only [Nat.zero_max, max_assoc, max_self] using hAFd
    obtain ⟨B, hBc, hBd, hB⟩ := hFormat AΓ AF Γ
      (scalarFunctionGraph Set.univ (fun x => eval x (jointPolynomial S0 i)))
      hcard hdegree hΓ hAFc' hAFd' hAF
    refine ⟨B, scalarRelationComposition Γ
      (scalarFunctionGraph Set.univ (fun x => eval x (jointPolynomial S0 i))),
      hBc, hBd, hB, ?_⟩
    intro t ht y
    simpa only [jointPolynomial_eval] using
      composition_graph hgraph (jointPolynomial S0 i) t (hinside ht) y

end PaperI.SectionIntegralReadouts
