import PaperILean.BoundedDistanceGraph

/-! I1259: project the original bounded-search graph, retaining both strict
band endpoints and both radius parameters in one joint definable family. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarBoundedBand (S : Set (Fin 2 → ℝ)) (T W : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∃ r : ℝ, Sum.elim (fun _ : Unit => r) x ∈
    planarBoundedSquaredDistanceGraph S T ∧ W/2 < r ∧ r < 4*W}

theorem planarBoundedBand_subset_box (S : Set (Fin 2 → ℝ)) (T W : ℝ) :
    planarBoundedBand S T W ⊆ planarCoordinateBox T := by
  rintro x ⟨r,hr,_,_⟩
  exact hr.2.1

theorem planarBoundedBand_eq_empty_of_nonpos_width
    (S : Set (Fin 2 → ℝ)) (T : ℝ) {W : ℝ} (hW : W ≤ 0) :
    planarBoundedBand S T W = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  rintro x ⟨r,hr,_,hhi⟩
  have hnonneg : 0 ≤ r := hr.2.2.1
  linarith

theorem planarBoundedBand_eq_empty_of_neg_radius
    (S : Set (Fin 2 → ℝ)) {T : ℝ} (hT : T < 0) (W : ℝ) :
    planarBoundedBand S T W = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  rintro x ⟨r,hr,_,_⟩
  exact (not_le_of_gt hT) hr.1

theorem bufferedDistanceBand_coordinates_eq_boundedBand
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox T) :
    (WithLp.equiv 2 (Fin 2 → ℝ)) '' bufferedDistanceBand E W =
      planarBoundedBand ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) T W := by
  ext x
  change x ∈ _ ↔ ∃ r : ℝ, _ ∧ _
  rw [← planarBoxDistanceGraph_eq_boundedSquaredDistanceGraph ho hbox]
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨Metric.infDist y Eᶜ,⟨hT,?_,?_⟩,hy⟩
    · exact hbox ⟨y,bufferedDistanceBand_subset E hW.le hy,rfl⟩
    · change Metric.infDist y Eᶜ = Metric.infDist
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ((WithLp.equiv 2 (Fin 2 → ℝ)) y)) Eᶜ
      rw [Equiv.symm_apply_apply]
  · rintro ⟨r,⟨_,_,hr⟩,hlo,hhi⟩
    refine ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm x,?_,by simp⟩
    change W/2 < _ ∧ _ < 4*W
    change r = Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm x) Eᶜ at hr
    exact hr ▸ ⟨hlo,hhi⟩

def planarBoundedBandFamily {ρ : Type*} (G : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set ((((ρ ⊕ Unit) ⊕ Unit) ⊕ Fin 2) → ℝ) :=
  {v | (fun i => v (Sum.inr i)) ∈ planarBoundedBand
    (projectionFiber G (fun i => v (Sum.inl (Sum.inl (Sum.inl i)))))
    (v (Sum.inl (Sum.inl (Sum.inr ())))) (v (Sum.inl (Sum.inr ())))}

theorem planarBoundedBandFamily_fiber {ρ : Type*}
    (G : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) (T W : ℝ) :
    projectionFiber (planarBoundedBandFamily G)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) =
      planarBoundedBand (projectionFiber G p) T W := rfl

theorem planarBoundedBandFamily_definable {ρ : Type*} [Finite ρ]
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (planarBoundedBandFamily G) := by
  let β := ((ρ ⊕ Unit) ⊕ Unit) ⊕ Fin 2
  let e : ((ρ ⊕ Unit) ⊕ (Unit ⊕ Fin 2)) → β ⊕ Unit :=
    Sum.elim (fun i => Sum.inl (Sum.inl (Sum.inl i)))
      (Sum.elim Sum.inr (fun i => Sum.inl (Sum.inr i)))
  let w : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ())))
  let r : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inr ())
  have h := realDefinable_exists
    (((planarBoundedSquaredDistanceGraphFamily_definable hG).preimage_comp e).inter
      ((realPolynomial_lt_definable w (2*r)).inter (realPolynomial_lt_definable r (4*w))))
  convert h using 1
  ext v
  change (∃ a : ℝ, _ ∧ _ ∧ _) ↔ (∃ a : Unit → ℝ, _ ∧ _ ∧ _)
  simp only [mem_preimage,planarBoundedSquaredDistanceGraphFamily,mem_setOf_eq,
    Function.comp_def,e,Sum.elim_inl,Sum.elim_inr,w,r,MvPolynomial.eval_X,map_mul,map_ofNat]
  constructor
  · rintro ⟨a,ha,hl,hu⟩
    exact ⟨fun _ => a,ha,by linarith,hu⟩
  · rintro ⟨a,ha,hl,hu⟩
    refine ⟨a (),?_,by linarith,hu⟩
    convert ha using 1
    congr 1
    funext i
    cases i with
    | inl u => cases u; rfl
    | inr i => rfl

theorem published_planarBoundedBandFamily_uniform_format
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] (G : Set ((ρ ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ s D : ℕ, ∀ (p : ρ → ℝ) (T W : ℝ),
      ∃ A : Finset (MvPolynomial (Fin 2) ℝ), A.card ≤ s ∧
        (∀ q ∈ A, q.totalDegree ≤ D) ∧
        PolynomialSignDetermined A (planarBoundedBand (projectionFiber G p) T W) := by
  obtain ⟨s,D,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (hQE.finite_sign_description _ (planarBoundedBandFamily_definable hG))
  exact ⟨s,D,fun p T W => h (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))⟩

end PaperI
