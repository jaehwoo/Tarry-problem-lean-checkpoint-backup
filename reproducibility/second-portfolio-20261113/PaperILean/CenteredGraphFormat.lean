import PaperILean.PolynomialSignPullbackDegree
import PaperILean.CenteredPreparationAmplitude

/-! Vertical translation of the represented graph preserves its format bounds.
The translated scalar is auxiliary; the geometric centerline is not redefined. -/

noncomputable section
namespace PaperI
open Set

def centeredGraphRelation (S : Set (Fin 2 → ℝ)) (c : ℝ) : Set (Fin 2 → ℝ) :=
  {v | ![v 0,v 1+c] ∈ S}

theorem centeredGraphRelation_realize_iff (S : Set (Fin 2 → ℝ))
    (f : ℝ → ℝ) (J : Set ℝ) (hrep : ∀ x ∈ J, ∀ y : ℝ, ![x,y] ∈ S ↔ y=f x)
    (c x y : ℝ) (hx : x ∈ J) :
    ![x,y] ∈ centeredGraphRelation S c ↔ y=f x-c := by
  change ![x,y+c] ∈ S ↔ _
  rw [hrep x hx]
  exact eq_sub_iff_add_eq.symm

theorem centeredGraphRelation_bounded_format
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (S : Set (Fin 2 → ℝ))
    (s D : ℕ) (hc : A.card ≤ s) (hd : ∀ p ∈ A, p.totalDegree ≤ D)
    (hS : PolynomialSignDetermined A S) (c : ℝ) :
    ∃ B : Finset (MvPolynomial (Fin 2) ℝ), B.card ≤ s ∧
      (∀ p ∈ B, p.totalDegree ≤ D) ∧ PolynomialSignDetermined B (centeredGraphRelation S c) := by
  let q : Fin 2 → MvPolynomial (Fin 2) ℝ :=
    ![MvPolynomial.X 0,MvPolynomial.X 1+MvPolynomial.C c]
  have hq : ∀ i, (q i).totalDegree ≤ 1 := by
    intro i
    fin_cases i
    · simp [q]
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp [q])
  obtain ⟨B,hBc,hBd,hB⟩ := polynomial_preimage_bounded_sign_format
    A S s D 1 hc hd hS q hq
  refine ⟨B,hBc,by simpa only [Nat.mul_one] using hBd,?_⟩
  convert hB using 1
  ext v
  have he : (fun i => MvPolynomial.eval v (q i)) = ![v 0,v 1+c] := by
    funext i
    fin_cases i <;> simp [q]
  simp only [centeredGraphRelation,mem_setOf_eq,he]

end PaperI
