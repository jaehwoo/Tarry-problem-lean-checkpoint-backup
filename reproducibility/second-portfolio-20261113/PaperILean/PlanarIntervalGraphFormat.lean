import PaperILean.PlanarCylindricalCellGeometry
import PaperILean.PolynomialSignPullbackDegree
import PaperILean.ClosedArcGraphFormat

/-! Recover the two scalar graph formats directly from the actual planar image
and its original-coordinate parameter. The parameter coordinate uses y=x;
the other coordinate is a linear pullback of the image. No new QE input or
separately chosen graph family is needed. -/
noncomputable section
namespace PaperI
open Set

theorem planar_interval_graph_scalar_format
    {S : Set (Fin 2 → ℝ)} {γ : ℝ → Fin 2 → ℝ} {a b : ℝ} (j : Fin 2)
    (ht : ∀ t ∈ Ioo a b, γ t j = t) (himage : S = γ '' Ioo a b)
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (s D : ℕ) (hc : A.card ≤ s)
    (hd : ∀ q ∈ A, q.totalDegree ≤ D) (hS : PolynomialSignDetermined A S) :
    ∀ i, ∃ (B : Finset (MvPolynomial (Fin 2) ℝ)) (G : Set (Fin 2 → ℝ)),
      B.card ≤ max s 1 ∧ (∀ q ∈ B, q.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B G ∧
      ∀ x ∈ Ioo a b, ∀ y : ℝ, ![x,y] ∈ G ↔ y = γ x i := by
  classical
  intro i
  by_cases hij : i = j
  · subst i
    let q : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 - MvPolynomial.X 0
    refine ⟨{q}, {v | v 1 = v 0}, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.card_singleton] using (le_max_right s 1)
    · intro r hr
      have hrq : r = q := Finset.mem_singleton.mp hr
      subst r
      exact ((MvPolynomial.totalDegree_sub _ _).trans (by simp :
        max (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1)).trans (le_max_right D 1)
    · simpa only [q, map_sub, MvPolynomial.eval_X, sub_eq_zero] using polynomialSignDetermined_zero q
    · intro x hx y
      simp only [mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ht x hx]
  · let q : Fin 2 → MvPolynomial (Fin 2) ℝ := fun k => MvPolynomial.X (if k = j then 0 else 1)
    obtain ⟨B,hBc,hBd,hB⟩ := polynomial_preimage_bounded_sign_format A S s D 1 hc hd hS q
      (fun k => by simp only [q, MvPolynomial.totalDegree_X]; exact le_rfl)
    let G : Set (Fin 2 → ℝ) := {v | (fun k => v (if k = j then 0 else 1)) ∈ S}
    refine ⟨B,G,hBc.trans (le_max_left s 1),?_,?_,?_⟩
    · intro r hr
      have hrD : r.totalDegree ≤ D := by simpa only [Nat.mul_one] using hBd r hr
      exact hrD.trans (le_max_left D 1)
    · simpa only [q,MvPolynomial.eval_X] using hB
    · intro x hx y
      change (fun k => (![x,y] : Fin 2 → ℝ) (if k = j then 0 else 1)) ∈ S ↔ y = γ x i
      rw [himage]
      constructor
      · rintro ⟨t,ht',he⟩
        have htx : t = x := by
          have h := congrFun he j
          simpa only [ht t ht', if_pos rfl, Matrix.cons_val_zero] using h
        subst t
        have h := congrFun he i
        simpa only [if_neg hij, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h.symm
      · intro hy
        refine ⟨x,hx,?_⟩
        funext k
        by_cases hkj : k = j
        · subst k
          simpa only [if_true, Matrix.cons_val_zero] using ht x hx
        · have hki : k = i := by
            fin_cases k <;> fin_cases i <;> fin_cases j <;> simp_all
          subst k
          simpa only [if_neg hij, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hy.symm

theorem planar_interval_graph_eq_image_readout
    {S : Set (Fin 2 → ℝ)} {γ : ℝ → Fin 2 → ℝ} {U : Set ℝ} (j : Fin 2)
    (ht : ∀ t ∈ U, γ t j = t) (himage : S = γ '' U) :
    parametrizedArcGraph γ U =
      {v : (Unit ⊕ Fin 2) → ℝ | v ∘ Sum.inr ∈ S ∧ v (Sum.inl ()) = v (Sum.inr j)} := by
  ext v
  rw [mem_parametrizedArcGraph]
  constructor
  · rintro ⟨hv,hcoord⟩
    have he : v ∘ Sum.inr = γ (v (Sum.inl ())) := funext hcoord
    refine ⟨?_, ?_⟩
    · rw [himage]
      exact ⟨v (Sum.inl ()),hv,he.symm⟩
    · rw [hcoord j,ht _ hv]
  · rintro ⟨hv,hcoord⟩
    rw [himage] at hv
    obtain ⟨t,ht',he⟩ := hv
    have htime : v (Sum.inl ()) = t := by
      exact hcoord.trans ((congrFun he j).symm.trans (ht t ht'))
    rw [htime]
    exact ⟨ht',fun i => (congrFun he i).symm⟩

/-- Joint graph format is bounded by (s+1,max D 1), independently of endpoints
and coefficients. The added atom records the original parameter coordinate. -/
theorem planar_interval_graph_joint_format
    {S : Set (Fin 2 → ℝ)} {γ : ℝ → Fin 2 → ℝ} {U : Set ℝ} (j : Fin 2)
    (ht : ∀ t ∈ U, γ t j = t) (himage : S = γ '' U)
    (A : Finset (MvPolynomial (Fin 2) ℝ)) (s D : ℕ) (hc : A.card ≤ s)
    (hd : ∀ q ∈ A, q.totalDegree ≤ D) (hS : PolynomialSignDetermined A S) :
    ∃ B : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), B.card ≤ s + 1 ∧
      (∀ q ∈ B, q.totalDegree ≤ max D 1) ∧
      PolynomialSignDetermined B (parametrizedArcGraph γ U) := by
  classical
  obtain ⟨B,hBc,hBd,hB⟩ := polynomial_preimage_bounded_sign_format A S s D 1 hc hd hS
    (fun i => MvPolynomial.X (Sum.inr i : Unit ⊕ Fin 2)) (fun _ => by simp)
  let q : MvPolynomial (Unit ⊕ Fin 2) ℝ := MvPolynomial.X (Sum.inl ()) - MvPolynomial.X (Sum.inr j)
  have hqd : q.totalDegree ≤ 1 := (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  refine ⟨B ∪ {q}, ?_, ?_, ?_⟩
  · exact (Finset.card_union_le B {q}).trans (by simpa only [Finset.card_singleton] using Nat.add_le_add_right hBc 1)
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · have hrD : r.totalDegree ≤ D := by simpa only [Nat.mul_one] using hBd r hr
      exact hrD.trans (le_max_left D 1)
    · rw [Finset.mem_singleton.mp hr]
      exact hqd.trans (le_max_right D 1)
  · rw [planar_interval_graph_eq_image_readout j ht himage]
    intro x y hxy
    have hs := hB x y (fun r hr => hxy r (Finset.mem_union_left _ hr))
    have he := (hxy q (Finset.mem_union_right _ (Finset.mem_singleton_self _))).1
    simp only [q,map_sub,MvPolynomial.eval_X,sub_eq_zero] at he
    simpa only [MvPolynomial.eval_X,Function.comp_def,mem_setOf_eq] using and_congr hs he

end PaperI
