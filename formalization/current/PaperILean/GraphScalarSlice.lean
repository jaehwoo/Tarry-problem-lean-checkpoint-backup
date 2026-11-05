import PaperILean.PublishedScalarMonotonicity
import PaperILean.PolynomialFiberFormat
import PaperILean.PublishedRealAlgebraicAssumptions

/-! Restrict a parameter slice of an actual graph to an open scalar interval.
Only graph correctness on the stated closed interval is required. Values
outside that interval, including arbitrary extensions of f, play no role. -/

noncomputable section
namespace PaperI
open FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem openScalarGraph_eq_empty_of_le (f : ℝ → ℝ) {a b : ℝ} (h : b ≤ a) :
    openScalarGraph f a b = ∅ := by
  ext v
  simp only [openScalarGraph, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha, hb, _⟩
  exact (not_lt_of_ge h) (ha.trans hb)

/-- No finite base-coordinate premise or positivity of b-a is needed once the
joint graph already has a finite polynomial-sign description. -/
theorem openScalarGraph_has_sign_description_of_joint_graph
    {α : Type*} {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : HasPolynomialSignDescription G) (p : α → ℝ)
    (f : ℝ → ℝ) (a b : ℝ)
    (hGrep : ∀ t ∈ Set.Icc a b, ∀ y : ℝ,
      Sum.elim p ![t, y] ∈ G ↔ y = f t) :
    HasPolynomialSignDescription (openScalarGraph f a b) := by
  classical
  obtain ⟨A, hA⟩ := hG
  have hSlice := polynomialSignDetermined_projectionFiber p A G hA
  have ha := polynomialSignDetermined_pos
    (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a)
  have hb := polynomialSignDetermined_pos
    (MvPolynomial.C b - MvPolynomial.X (0 : Fin 2))
  have hEq : openScalarGraph f a b =
      (projectionFiber G p ∩ {x | 0 < MvPolynomial.eval x
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a)}) ∩
      {x | 0 < MvPolynomial.eval x (MvPolynomial.C b - MvPolynomial.X (0 : Fin 2))} := by
    ext v
    have hv : ![v 0, v 1] = v := by
      funext i
      fin_cases i <;> simp
    simp only [Set.mem_inter_iff, projectionFiber, Set.mem_setOf_eq, map_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C, sub_pos, openScalarGraph]
    constructor
    · rintro ⟨ha, hb, hy⟩
      exact ⟨⟨by simpa only [hv] using (hGrep (v 0) ⟨ha.le, hb.le⟩ (v 1)).mpr hy, ha⟩, hb⟩
    · rintro ⟨⟨hmem, ha⟩, hb⟩
      exact ⟨ha, hb, (hGrep (v 0) ⟨ha.le, hb.le⟩ (v 1)).mp (by simpa only [hv] using hmem)⟩
  rw [hEq]
  exact ⟨_, polynomialSignDetermined_inter (polynomialSignDetermined_inter hSlice ha) hb⟩

/-- Apply the accepted qualitative QE input to the joint definable relation,
then specialize and restrict it using the local graph identity. -/
theorem published_openScalarGraph_sign_description
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] {G : Set ((α ⊕ Fin 2) → ℝ)}
    (hG : (Set.univ : Set ℝ).Definable Language.ring G) (p : α → ℝ)
    (f : ℝ → ℝ) (a b : ℝ)
    (hGrep : ∀ t ∈ Set.Icc a b, ∀ y : ℝ,
      Sum.elim p ![t, y] ∈ G ↔ y = f t) :
    HasPolynomialSignDescription (openScalarGraph f a b) :=
  openScalarGraph_has_sign_description_of_joint_graph
    (hQE.finite_sign_description G hG) p f a b hGrep

end PaperI
