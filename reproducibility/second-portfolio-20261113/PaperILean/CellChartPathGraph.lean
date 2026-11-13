import PaperILean.CellChartInterpolation
import PaperILean.SemialgebraicRelationComposition
import PaperILean.PublishedRealAlgebraicAssumptions
import PaperILean.SemialgebraicPathData

/-! One actual graph with both physical endpoints free. A single witness
contains the two inverse-chart coordinates and their interpolated coordinate.
Qualitative QE is retained explicitly; the final format bound is uniform in
the endpoints of this fixed chart, not yet in coefficient/CAD parameters. -/

noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cubeChartPathRelation {α : Type*} {d : ℕ}
    (G : Set ((Fin d ⊕ α) → ℝ)) : Set (((α ⊕ α) ⊕ (Unit ⊕ α)) → ℝ) :=
  {x | x (Sum.inr (Sum.inl ())) ∈ Icc (0 : ℝ) 1 ∧
    ∃ w : (Fin 3 × Fin d) → ℝ,
      Sum.elim (fun i => w (0,i)) (fun i => x (Sum.inl (Sum.inl i))) ∈ G ∧
      Sum.elim (fun i => w (1,i)) (fun i => x (Sum.inl (Sum.inr i))) ∈ G ∧
      Sum.elim (fun i => w (2,i)) (fun i => x (Sum.inr (Sum.inr i))) ∈ G ∧
      ∀ i, w (2,i) = (1 - x (Sum.inr (Sum.inl ()))) * w (0,i) +
        x (Sum.inr (Sum.inl ())) * w (1,i)}

theorem cubeChartPathRelation_definable {α : Type*} [Finite α] {d : ℕ}
    {G : Set ((Fin d ⊕ α) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    (univ : Set ℝ).Definable Language.ring (cubeChartPathRelation G) := by
  let δ := (α ⊕ α) ⊕ (Unit ⊕ α)
  let β := Fin 3 × Fin d
  let e0 : Fin d ⊕ α → δ ⊕ β :=
    Sum.elim (fun i => Sum.inr (0,i)) (fun i => Sum.inl (Sum.inl (Sum.inl i)))
  let e1 : Fin d ⊕ α → δ ⊕ β :=
    Sum.elim (fun i => Sum.inr (1,i)) (fun i => Sum.inl (Sum.inl (Sum.inr i)))
  let e2 : Fin d ⊕ α → δ ⊕ β :=
    Sum.elim (fun i => Sum.inr (2,i)) (fun i => Sum.inl (Sum.inr (Sum.inr i)))
  let T : MvPolynomial (δ ⊕ β) ℝ := MvPolynomial.X (Sum.inl (Sum.inr (Sum.inl ())))
  let Q (i : Fin d) : MvPolynomial (δ ⊕ β) ℝ :=
    MvPolynomial.X (Sum.inr (2,i)) -
      ((1 - T) * MvPolynomial.X (Sum.inr (0,i)) + T * MvPolynomial.X (Sum.inr (1,i)))
  have hEq := realDefinable_finite_all (fun i : Fin d => realPolynomial_zero_definable (Q i))
  have h := realDefinable_exists
    (((hG.preimage_comp e0).inter ((hG.preimage_comp e1).inter (hG.preimage_comp e2))).inter hEq)
  have ht : (univ : Set ℝ).Definable Language.ring
      {x : δ → ℝ | x (Sum.inr (Sum.inl ())) ∈ Icc (0 : ℝ) 1} := by
    have h0 := realPolynomial_nonneg_definable
      (MvPolynomial.X (Sum.inr (Sum.inl ())) : MvPolynomial δ ℝ)
    have h1 := realPolynomial_nonneg_definable
      (1 - MvPolynomial.X (Sum.inr (Sum.inl ())) : MvPolynomial δ ℝ)
    simpa only [Set.inter_def, Set.mem_setOf_eq, MvPolynomial.eval_X, map_sub, map_one,
      sub_nonneg, Set.mem_Icc] using h0.inter h1
  convert ht.inter h using 1
  ext x
  apply and_congr_right
  intro _
  apply exists_congr
  intro w
  have he0 : Sum.elim x w ∘ e0 =
      Sum.elim (fun i => w (0,i)) (fun i => x (Sum.inl (Sum.inl i))) := by
    funext i; cases i <;> rfl
  have he1 : Sum.elim x w ∘ e1 =
      Sum.elim (fun i => w (1,i)) (fun i => x (Sum.inl (Sum.inr i))) := by
    funext i; cases i <;> rfl
  have he2 : Sum.elim x w ∘ e2 =
      Sum.elim (fun i => w (2,i)) (fun i => x (Sum.inr (Sum.inr i))) := by
    funext i; cases i <;> rfl
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, he0, he1, he2,
    Q, T, map_sub, map_add, map_mul, map_one, MvPolynomial.eval_X,
    Sum.elim_inl, Sum.elim_inr, sub_eq_zero, and_assoc]

theorem cubeMapGraph_chart_mem_iff {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (u : Fin d → ℝ) (a : C) :
    Sum.elim u a.val ∈ cubeMapGraph (fun x => (e x).val) ↔ u = (e.symm a).val := by
  constructor
  · rintro ⟨hu, he⟩
    have h : e ⟨u, hu⟩ = a := Subtype.ext he
    have hinv : (⟨u, hu⟩ : openUnitCube d) = e.symm a := e.injective (h.trans (e.apply_symm_apply a).symm)
    exact congrArg Subtype.val hinv
  · intro h
    subst u
    exact ⟨(e.symm a).property, congrArg Subtype.val (e.apply_symm_apply a)⟩

theorem cubeChartPathRelation_chart_mem {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) (t : ℝ) (z : α → ℝ) :
    Sum.elim (Sum.elim a.val b.val) (Sum.elim (fun _ => t) z) ∈
      cubeChartPathRelation (cubeMapGraph (fun x => (e x).val)) ↔
      t ∈ Icc (0 : ℝ) 1 ∧ z = cellChartPath e a b t := by
  change (t ∈ Icc (0 : ℝ) 1 ∧ ∃ w : (Fin 3 × Fin d) → ℝ,
    Sum.elim (fun i => w (0,i)) a.val ∈ cubeMapGraph (fun x => (e x).val) ∧
    Sum.elim (fun i => w (1,i)) b.val ∈ cubeMapGraph (fun x => (e x).val) ∧
    Sum.elim (fun i => w (2,i)) z ∈ cubeMapGraph (fun x => (e x).val) ∧
    ∀ i, w (2,i) = (1-t)*w (0,i)+t*w (1,i)) ↔ _
  constructor
  · rintro ⟨ht,w,h0,h1,⟨h2,hz⟩,hw⟩
    have hu := (cubeMapGraph_chart_mem_iff e _ a).mp h0
    have hv := (cubeMapGraph_chart_mem_iff e _ b).mp h1
    have heq : (⟨fun i => w (2,i),h2⟩ : openUnitCube d) =
        cubeSegment (e.symm a) (e.symm b) ⟨t,ht⟩ := by
      apply Subtype.ext
      funext i
      change w (2,i) = (1-t)*(e.symm a).val i+t*(e.symm b).val i
      rw [hw i, ← congrFun hu i, ← congrFun hv i]
    refine ⟨ht, ?_⟩
    rw [cellChartPath_eq e a b ht, ← heq]
    exact hz.symm
  · rintro ⟨ht,hz⟩
    let u := e.symm a
    let v := e.symm b
    let c := cubeSegment u v ⟨t,ht⟩
    let w : (Fin 3 × Fin d) → ℝ := fun p => ![u.val,v.val,c.val] p.1 p.2
    refine ⟨ht,w,?_,?_,?_,?_⟩
    · exact (cubeMapGraph_chart_mem_iff e _ a).mpr rfl
    · exact (cubeMapGraph_chart_mem_iff e _ b).mpr rfl
    · refine ⟨c.property, ?_⟩
      exact (cellChartPath_eq e a b ht).symm.trans hz.symm
    · intro i
      rfl

theorem cubeChartPathRelation_valid_endpoints {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b z : α → ℝ) (t : ℝ)
    (h : Sum.elim (Sum.elim a b) (Sum.elim (fun _ => t) z) ∈
      cubeChartPathRelation (cubeMapGraph (fun x => (e x).val))) : a ∈ C ∧ b ∈ C := by
  obtain ⟨_,w,⟨hu,ha⟩,⟨hv,hb⟩,_⟩ := h
  change (e ⟨fun i => w (0,i),hu⟩).val = a at ha
  change (e ⟨fun i => w (1,i),hv⟩).val = b at hb
  exact ⟨ha ▸ (e ⟨_,hu⟩).property, hb ▸ (e ⟨_,hv⟩).property⟩

theorem cubeChartPathRelation_actual_graph {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b z : α → ℝ) (t : ℝ) :
    Sum.elim (Sum.elim a b) (Sum.elim (fun _ => t) z) ∈
      cubeChartPathRelation (cubeMapGraph (fun x => (e x).val)) ↔
      ∃ (ha : a ∈ C) (hb : b ∈ C), t ∈ Icc (0 : ℝ) 1 ∧
        z = cellChartPath e ⟨a,ha⟩ ⟨b,hb⟩ t := by
  constructor
  · intro h
    obtain ⟨ha,hb⟩ := cubeChartPathRelation_valid_endpoints e a b z t h
    exact ⟨ha,hb,(cubeChartPathRelation_chart_mem e ⟨a,ha⟩ ⟨b,hb⟩ t z).mp h⟩
  · rintro ⟨ha,hb,h⟩
    exact (cubeChartPathRelation_chart_mem e ⟨a,ha⟩ ⟨b,hb⟩ t z).mpr h

theorem cubeChartPathRelation_fiber {α : Type*} {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C) (a b : C) :
    projectionFiber (cubeChartPathRelation (cubeMapGraph (fun x => (e x).val)))
      (Sum.elim a.val b.val) = unitPathGraph (cellChartPath e a b) := by
  ext v
  have hv : Sum.elim (fun _ : Unit => v (Sum.inl ())) (fun i => v (Sum.inr i)) = v := by
    funext i; rcases i with ⟨⟩ | i <;> rfl
  change Sum.elim (Sum.elim a.val b.val) v ∈
    cubeChartPathRelation (cubeMapGraph (fun x => (e x).val)) ↔
    v ∈ unitPathGraph (cellChartPath e a b)
  rw [← hv, cubeChartPathRelation_chart_mem, unitPathGraph_mem_iff]

theorem cellChartPath_joint_semialgebraic (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C)
    (he : HasPolynomialSignDescription (cubeMapGraph (fun x => (e x).val))) :
    HasPolynomialSignDescription (cubeChartPathRelation (cubeMapGraph (fun x => (e x).val))) :=
  hQE.finite_sign_description _
    (cubeChartPathRelation_definable (hasPolynomialSignDescription_definable he))

/-- The same graph is specialized for all endpoint pairs; s,D precede a,b.
These bounds depend on the fixed chart e, not just its cell dimension. -/
theorem semialgebraicCell_endpoint_path_family (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] {d : ℕ} {C : Set (α → ℝ)}
    (e : openUnitCube d ≃ₜ C)
    (he : HasPolynomialSignDescription (cubeMapGraph (fun x => (e x).val))) :
    ∃ s D : ℕ, ∀ a b : C,
      ContinuousOn (cellChartPath e a b) (Icc (0 : ℝ) 1) ∧
      MapsTo (cellChartPath e a b) (Icc (0 : ℝ) 1) C ∧
      cellChartPath e a b 0 = a.val ∧ cellChartPath e a b 1 = b.val ∧
      ∃ A : Finset (MvPolynomial (Unit ⊕ α) ℝ), A.card ≤ s ∧
        (∀ p ∈ A, p.totalDegree ≤ D) ∧ PolynomialSignDetermined A (unitPathGraph (cellChartPath e a b)) := by
  obtain ⟨s,D,h⟩ := hasPolynomialSignDescription_uniform_fiber_sign_format
    (cellChartPath_joint_semialgebraic hQE e he)
  refine ⟨s,D,fun a b => ⟨cellChartPath_continuousOn e a b,cellChartPath_mapsTo e a b,
    cellChartPath_source e a b,cellChartPath_target e a b,?_⟩⟩
  simpa only [cubeChartPathRelation_fiber] using h (Sum.elim a.val b.val)

end PaperI
