import PaperILean.BoundedDistanceMinimum
import PaperILean.DefinableDistanceBands

/-! Original I1259 bounded-search formula with coefficient and box-radius
parameters in one joint family. QE is the unchanged accepted named input.
Uniform format is extracted from the joint family, not separate fibers. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem polynomial_planarCoordinateBox_definable {α : Type*} [Finite α]
    (t : MvPolynomial α ℝ) (a : Fin 2 → α) :
    (univ : Set ℝ).Definable Language.ring
      {v : α → ℝ | (v ∘ a) ∈ planarCoordinateBox (MvPolynomial.eval v t)} := by
  have h := realDefinable_finite_all (fun j : Fin 2 =>
    (realPolynomial_le_definable (-t) (MvPolynomial.X (a j))).inter
      (realPolynomial_le_definable (MvPolynomial.X (a j)) t))
  simpa only [planarCoordinateBox,mem_setOf_eq,mem_inter_iff,
    Function.comp_def,abs_le,map_neg,MvPolynomial.eval_X] using h

def planarBoundedSquaredDistanceGraphFamily {ρ : Type*}
    (G : Set ((ρ ⊕ Fin 2) → ℝ)) : Set (((ρ ⊕ Unit) ⊕ (Unit ⊕ Fin 2)) → ℝ) :=
  {v | (fun i => v (Sum.inr i)) ∈ planarBoundedSquaredDistanceGraph
    (projectionFiber G (fun i => v (Sum.inl (Sum.inl i))))
    (v (Sum.inl (Sum.inr ())))}

theorem planarBoundedSquaredDistanceGraphFamily_fiber {ρ : Type*}
    (G : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) (T : ℝ) :
    projectionFiber (planarBoundedSquaredDistanceGraphFamily G)
      (Sum.elim p (fun _ => T)) =
      planarBoundedSquaredDistanceGraph (projectionFiber G p) T := rfl

theorem planarBoundedSquaredDistanceGraphFamily_definable {ρ : Type*} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring
      (planarBoundedSquaredDistanceGraphFamily G) := by
  let β := (ρ ⊕ Unit) ⊕ (Unit ⊕ Fin 2)
  let a : Fin 2 → β := fun j => Sum.inr (Sum.inr j)
  let t : MvPolynomial β ℝ := MvPolynomial.X (Sum.inl (Sum.inr ()))
  let r : MvPolynomial β ℝ := MvPolynomial.X (Sum.inr (Sum.inl ()))
  let t' : MvPolynomial (β ⊕ Fin 2) ℝ := MvPolynomial.rename Sum.inl t
  let r' : MvPolynomial (β ⊕ Fin 2) ℝ := MvPolynomial.rename Sum.inl r
  let e : ρ ⊕ Fin 2 → β ⊕ Fin 2 := Sum.elim
    (fun i => Sum.inl (Sum.inl (Sum.inl i))) Sum.inr
  let q := planarSquaredDistPolynomial (fun j => Sum.inl (a j)) Sum.inr
  have ht := realPolynomial_nonneg_definable t
  have hx := polynomial_planarCoordinateBox_definable t a
  have hr := realPolynomial_nonneg_definable r
  have hb := polynomial_planarCoordinateBox_definable (4*t'+1) (Sum.inr : Fin 2 → β ⊕ Fin 2)
  have he := (hG.preimage_comp e).compl
  have ha := realDefinable_exists (hb.inter (he.inter (realPolynomial_zero_definable (r'^2-q))))
  have hl := realDefinable_forall ((hb.inter he).compl.union (realPolynomial_le_definable (r'^2) q))
  convert ht.inter (hx.inter (hr.inter (ha.inter hl))) using 1
  ext v
  have heq (y : Fin 2 → ℝ) : Sum.elim v y ∘ e =
      Sum.elim (fun i => v (Sum.inl (Sum.inl i))) y := by
    funext i
    cases i <;> rfl
  simp only [planarBoundedSquaredDistanceGraphFamily,planarBoundedSquaredDistanceGraph,
    projectionFiber,mem_setOf_eq,mem_inter_iff,mem_compl_iff,mem_union,mem_preimage,
    heq,t,r,t',r',a,q,planarSquaredDistPolynomial_eval,
    map_sub,map_pow,map_add,map_mul,map_ofNat,map_one,MvPolynomial.eval_X,
    MvPolynomial.eval_rename,Function.comp_def,Sum.elim_inl,Sum.elim_inr,sub_eq_zero]
  simp only [Function.comp_def] at heq
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr
  · apply exists_congr
    intro y
    rw [heq]
  · apply forall_congr'
    intro y
    rw [heq]
    tauto

theorem published_planarBoundedSquaredDistanceGraphFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (T : ℝ),
      ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A
          (planarBoundedSquaredDistanceGraph (projectionFiber G p) T) := by
  obtain ⟨s,D,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (planarBoundedSquaredDistanceGraphFamily_definable hG))
  exact ⟨s,D,fun p T => h (Sum.elim p (fun _ => T))⟩

theorem published_planarBoxDistanceGraphFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (T : ℝ)
      (E : Set (WithLp 2 (Fin 2 → ℝ))), IsOpen E →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G p →
      (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T →
      ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (planarBoxDistanceGraph E T) := by
  obtain ⟨s,D,h⟩ := published_planarBoundedSquaredDistanceGraphFamily_uniform_format hQE G hG
  refine ⟨s,D,?_⟩
  intro p T E ho he hb
  rw [planarBoxDistanceGraph_eq_boundedSquaredDistanceGraph ho hb,he]
  exact h p T

theorem published_planarBoxDistanceGraph_has_sign_description
    (hQE : PublishedRealSemialgebraicity)
    {T : ℝ} {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T)
    (hE : HasPolynomialSignDescription ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E)) :
    HasPolynomialSignDescription (planarBoxDistanceGraph E T) := by
  let G : Set ((Empty ⊕ Fin 2) → ℝ) :=
    {v | (fun i => v (Sum.inr i)) ∈ (WithLp.equiv 2 (Fin 2 → ℝ)) '' E}
  have hG : (univ : Set ℝ).Definable Language.ring G :=
    (hasPolynomialSignDescription_definable hE).preimage_comp Sum.inr
  obtain ⟨_,_,h⟩ := published_planarBoxDistanceGraphFamily_uniform_format hQE G hG
  obtain ⟨A,_,_,hA⟩ := h (fun e => nomatch e) T E ho rfl hbox
  exact ⟨A,hA⟩

end PaperI
