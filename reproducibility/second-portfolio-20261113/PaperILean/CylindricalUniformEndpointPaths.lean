import PaperILean.CylindricalMixedFiberPaths
import PaperILean.UniversalSignFamily
import PaperILean.BoundedPolynomialTuple

/-! Uniform endpoint path graph format from the original cell/curve-selection
route. The universal coefficient family may have disconnected fibers. Bounds
are selected before coefficients, Boolean tables, represented sets and endpoints.
No Hardt triviality or published endpoint-path conclusion is used. -/

noncomputable section
namespace PaperI
open Set
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
attribute [local instance 2000] Classical.typeDecidableEq

theorem published_cylindrical_bounded_tuple_path_format
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (n s D : ℕ) :
    ∃ sPath dPath : ℕ, ∀ (P : Fin s → MvPolynomial (Fin n) ℝ),
      (∀ i, (P i).totalDegree ≤ D) → ∀ S : Set (Fin n → ℝ),
      PolynomialSignDetermined (Finset.univ.image P) S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
        ∃ A : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), A.card ≤ sPath ∧
          (∀ v ∈ A, v.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined A (unitPathGraph γ.toFun) := by
  classical
  have h := fun q : (Fin s → Bool × Bool) → Bool =>
    published_cylindrical_family_uniform_endpoint_path_format hCAD hQE n
      (universalPolynomialBooleanSet (Fin n) s D q)
      (universalPolynomialBooleanSet_hasPolynomialSignDescription (Fin n) s D q)
  choose sp dp hFmt using h
  refine ⟨Finset.univ.sup sp, Finset.univ.sup dp, ?_⟩
  intro P hP S hS hc a ha b hb
  have hSnative : PolynomialSignDetermined
      (@Finset.image (Fin s) (MvPolynomial (Fin n) ℝ)
        (fun a b => a.decidableEqMvPolynomial b) P Finset.univ) S := by
    have he := congrArg (fun dec : DecidableEq (MvPolynomial (Fin n) ℝ) =>
      PolynomialSignDetermined (@Finset.image (Fin s) (MvPolynomial (Fin n) ℝ)
        dec P Finset.univ) S)
      (Subsingleton.elim (Classical.typeDecidableEq (MvPolynomial (Fin n) ℝ))
        (fun a b => a.decidableEqMvPolynomial b))
    exact he.mp hS
  obtain ⟨q,hEq⟩ := polynomialSignDetermined_exists_universal_fiber s D P hP S hSnative
  have hEq' : S = projectionFiber (universalPolynomialBooleanSet (Fin n) s D q)
      (polynomialFamilyCoefficients D P) := hEq
  rw [hEq'] at hc ha hb ⊢
  obtain ⟨γ,A,hcard,hdegree,hA⟩ := hFmt q (polynomialFamilyCoefficients D P) hc a ha b hb
  exact ⟨γ,A,hcard.trans (Finset.le_sup (f := sp) (Finset.mem_univ q)),
    fun v hv => (hdegree v hv).trans (Finset.le_sup (f := dp) (Finset.mem_univ q)),hA⟩

/-- At-most input format permits zero atoms, degree zero, coefficient
cancellation and equal endpoints. No connectedness locus is assumed definable. -/
theorem published_cylindrical_bounded_sign_format_paths
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (n s D : ℕ) :
    ∃ sPath dPath : ℕ, ∀ (A : Finset (MvPolynomial (Fin n) ℝ)) (S : Set (Fin n → ℝ)),
      A.card ≤ s → (∀ v ∈ A, v.totalDegree ≤ D) →
      PolynomialSignDetermined A S → IsPreconnected S →
      ∀ a ∈ S, ∀ b ∈ S, ∃ γ : SemialgebraicUnitPath S a b,
        ∃ B : Finset (MvPolynomial (Unit ⊕ Fin n) ℝ), B.card ≤ sPath ∧
          (∀ v ∈ B, v.totalDegree ≤ dPath) ∧
          PolynomialSignDetermined B (unitPathGraph γ.toFun) := by
  obtain ⟨sp,dp,h⟩ := published_cylindrical_bounded_tuple_path_format hCAD hQE n s D
  refine ⟨sp,dp,?_⟩
  intro A S hcard hdegree hS hc a ha b hb
  obtain ⟨P,hP,hPS⟩ := exists_bounded_polynomial_tuple_of_signDetermined A S s D hcard hdegree hS
  have hPSclassical : PolynomialSignDetermined (Finset.univ.image P) S := by
    have he := congrArg (fun dec : DecidableEq (MvPolynomial (Fin n) ℝ) =>
      PolynomialSignDetermined (@Finset.image (Fin s) (MvPolynomial (Fin n) ℝ)
        dec P Finset.univ) S)
      (Subsingleton.elim (fun a b => a.decidableEqMvPolynomial b)
        (Classical.typeDecidableEq (MvPolynomial (Fin n) ℝ)))
    exact he.mp hPS
  exact h P hP S hPSclassical hc a ha b hb

end PaperI
