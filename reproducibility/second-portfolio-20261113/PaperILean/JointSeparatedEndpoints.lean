import PaperILean.JointEuclideanDiameter
import PaperILean.BufferedDistanceBandGeometry
import PaperILean.CylindricalDefinableChoice

/-! I1263/I1265: the original strict half-diameter endpoint choice, made
jointly. First select at a free positive comparison scale; then evaluate the
same selected map at the actual Borel diameter. No farthest pair, compact
component, or arbitrary extension of a restricted selector is assumed. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def planarSeparatedEndpointRelation {ρ : Type*} (H : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set (((ρ ⊕ Unit) ⊕ (Fin 2 ⊕ Fin 2)) → ℝ) :=
  {v | 0 < v (Sum.inl (Sum.inr ())) ∧
    Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
      (fun j => v (Sum.inr (Sum.inl j))) ∈ H ∧
    Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
      (fun j => v (Sum.inr (Sum.inr j))) ∈ H ∧
    (v (Sum.inl (Sum.inr ())))^2 < 4*planarSquaredDist
      (fun j => v (Sum.inr (Sum.inl j))) (fun j => v (Sum.inr (Sum.inr j)))}

theorem planarSeparatedEndpointRelation_mem_iff {ρ : Type*}
    (H : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) (r : ℝ)
    (a b : Fin 2 → ℝ) :
    Sum.elim (Sum.elim p (fun _ => r)) (Sum.elim a b) ∈
        planarSeparatedEndpointRelation H ↔
      0 < r ∧ a ∈ projectionFiber H p ∧ b ∈ projectionFiber H p ∧
        r/2 < dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm b) := by
  change (0 < r ∧ _ ∧ _ ∧ r^2 < 4*planarSquaredDist a b) ↔ _
  rw [planarSquaredDist_eq_dist_sq]
  have hd := dist_nonneg (x := (WithLp.equiv 2 (Fin 2 → ℝ)).symm a)
    (y := (WithLp.equiv 2 (Fin 2 → ℝ)).symm b)
  constructor
  · rintro ⟨hr,ha,hb,h⟩
    exact ⟨hr,ha,hb,by nlinarith⟩
  · rintro ⟨hr,ha,hb,h⟩
    exact ⟨hr,ha,hb,by nlinarith⟩

theorem planarSeparatedEndpointRelation_definable {ρ : Type*} [Finite ρ]
    {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hH : (univ : Set ℝ).Definable Language.ring H) :
    (univ : Set ℝ).Definable Language.ring (planarSeparatedEndpointRelation H) := by
  let a : ρ ⊕ Fin 2 → (ρ ⊕ Unit) ⊕ (Fin 2 ⊕ Fin 2) :=
    Sum.elim (fun r => Sum.inl (Sum.inl r)) (fun j => Sum.inr (Sum.inl j))
  let b : ρ ⊕ Fin 2 → (ρ ⊕ Unit) ⊕ (Fin 2 ⊕ Fin 2) :=
    Sum.elim (fun r => Sum.inl (Sum.inl r)) (fun j => Sum.inr (Sum.inr j))
  let r : MvPolynomial ((ρ ⊕ Unit) ⊕ (Fin 2 ⊕ Fin 2)) ℝ :=
    MvPolynomial.X (Sum.inl (Sum.inr ()))
  let q : MvPolynomial ((ρ ⊕ Unit) ⊕ (Fin 2 ⊕ Fin 2)) ℝ :=
    planarSquaredDistPolynomial (fun j => Sum.inr (Sum.inl j))
      (fun j => Sum.inr (Sum.inr j))
  have h := (realPolynomial_lt_definable 0 r).inter
    ((hH.preimage_comp a).inter ((hH.preimage_comp b).inter
      (realPolynomial_lt_definable (r^2) (4*q))))
  convert h using 1
  ext v
  have ha : v ∘ a = Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
      (fun j => v (Sum.inr (Sum.inl j))) := by funext i; cases i <;> rfl
  have hb : v ∘ b = Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
      (fun j => v (Sum.inr (Sum.inr j))) := by funext i; cases i <;> rfl
  simp only [planarSeparatedEndpointRelation,mem_setOf_eq,mem_inter_iff,
    mem_preimage,ha,hb,r,q,planarSquaredDistPolynomial_eval,map_zero,map_pow,
    map_mul,map_ofNat,MvPolynomial.eval_X,Function.comp_def]
  simp only [Function.comp_def] at ha hb
  rw [ha,hb]

theorem planarSeparatedEndpointRelation_nonpos {ρ : Type*}
    (H : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) {r : ℝ} (hr : r ≤ 0) :
    Sum.elim p (fun _ => r) ∉ projectionDomain (planarSeparatedEndpointRelation H) := by
  rintro ⟨x,hx⟩
  exact (not_lt_of_ge hr) hx.1

theorem planarSeparatedEndpointRelation_empty_fiber {ρ : Type*}
    (H : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ) (r : ℝ)
    (he : projectionFiber H p = ∅) :
    Sum.elim p (fun _ => r) ∉ projectionDomain (planarSeparatedEndpointRelation H) := by
  rintro ⟨x,hx⟩
  have ha : (fun j => x (Sum.inl j)) ∈ projectionFiber H p := hx.2.1
  rw [he] at ha
  exact ha

theorem planarSeparatedEndpointRelation_diameter_mem {ρ : Type*}
    (H : Set ((ρ ⊕ Fin 2) → ℝ)) (p : ρ → ℝ)
    (hb : Bornology.IsBounded ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p))
    (hp : 0 < planarFiberDiameter H p) :
    Sum.elim p (fun _ => planarFiberDiameter H p) ∈
      projectionDomain (planarSeparatedEndpointRelation H) := by
  obtain ⟨a,⟨x,hx,rfl⟩,b,⟨y,hy,rfl⟩,hne,hsep,hle⟩ :=
    exists_separated_pair_of_diam_pos hb hp
  exact ⟨Sum.elim x y,(planarSeparatedEndpointRelation_mem_iff H p _ x y).mpr
    ⟨hp,hx,hy,hsep⟩⟩

/-- One CAD choice is fixed over the entire parameter/scale domain. The
restricted graph is semialgebraic; no property off that domain is claimed. -/
theorem published_planarSeparatedEndpointSelector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    {ρ : Type} [Finite ρ] {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hH : HasPolynomialSignDescription H) :
    ∃ f : ((ρ ⊕ Unit) → ℝ) → (Fin 2 ⊕ Fin 2) → ℝ,
      HasPolynomialSignDescription
        (selectedFunctionGraph (projectionDomain (planarSeparatedEndpointRelation H)) f) ∧
      ∀ p ∈ projectionDomain (planarSeparatedEndpointRelation H),
        Sum.elim p (f p) ∈ planarSeparatedEndpointRelation H := by
  exact (hCAD.toDefinableChoice hQE).section_exists _
    (hQE.finite_sign_description _
      (planarSeparatedEndpointRelation_definable (hasPolynomialSignDescription_definable hH)))

def planarPositiveDiameterDomain {ρ : Type*} (H : Set ((ρ ⊕ Fin 2) → ℝ)) :
    Set (ρ → ℝ) := {p | 0 < planarFiberDiameter H p}

theorem published_planarPositiveDiameterDomain_measurable
    (hQE : PublishedRealSemialgebraicity) {ρ : Type} [Finite ρ]
    {H : Set ((ρ ⊕ Fin 2) → ℝ)} (hH : HasPolynomialSignDescription H)
    (hb : ∀ p, Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p)) :
    MeasurableSet (planarPositiveDiameterDomain H) :=
  measurableSet_lt measurable_const (published_planarFiberDiameter_measurable hQE hH hb)

/-- Both endpoints are selected once jointly in the coefficient parameters,
on the exact positive-diameter domain. The upper bound uses boundedness, not
an attained maximum. -/
theorem published_jointSeparatedEndpoints
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {H : Set ((ρ ⊕ Fin 2) → ℝ)}
    (hH : HasPolynomialSignDescription H)
    (hb : ∀ p, Bornology.IsBounded
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber H p)) :
    ∃ a b : planarPositiveDiameterDomain H → Fin 2 → ℝ,
      Measurable a ∧ Measurable b ∧
      ∀ p, a p ∈ projectionFiber H p.val ∧ b p ∈ projectionFiber H p.val ∧
        a p ≠ b p ∧
        planarFiberDiameter H p.val/2 <
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
            ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (a p))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (b p)) ≤ planarFiberDiameter H p.val := by
  letI : Fintype ρ := Fintype.ofFinite ρ
  obtain ⟨f,hf,hmem⟩ := published_planarSeparatedEndpointSelector hCAD hQE hH
  let g : planarPositiveDiameterDomain H →
      projectionDomain (planarSeparatedEndpointRelation H) := fun p =>
    ⟨Sum.elim p.val (fun _ => planarFiberDiameter H p.val),
      planarSeparatedEndpointRelation_diameter_mem H p.val (hb p.val) p.property⟩
  have hg : Measurable g := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl j => exact (measurable_pi_apply j).comp measurable_subtype_coe
    | inr u => exact (published_planarFiberDiameter_measurable hQE hH hb).comp measurable_subtype_coe
  have hm := (published_measurable_selected_function hQE hHardt _ f
    (hasPolynomialSignDescription_definable hf)).comp hg
  let a := fun p : planarPositiveDiameterDomain H => (f (g p).val) ∘ Sum.inl
  let b := fun p : planarPositiveDiameterDomain H => (f (g p).val) ∘ Sum.inr
  refine ⟨a,b,?_,?_,?_⟩
  · exact measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inl j)).comp hm)
  · exact measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inr j)).comp hm)
  · intro p
    have h := hmem (g p).val (g p).property
    have hfeta : f (g p).val = Sum.elim (a p) (b p) := by
      funext i; cases i <;> rfl
    rw [hfeta] at h
    obtain ⟨hp,ha,hb',hsep⟩ := (planarSeparatedEndpointRelation_mem_iff H p.val _ _ _).mp h
    refine ⟨ha,hb',?_,hsep,Metric.dist_le_diam_of_mem (hb p.val) ⟨a p,ha,rfl⟩ ⟨b p,hb',rfl⟩⟩
    intro he
    rw [he,dist_self] at hsep
    linarith

theorem jointEndpointPair_graph_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω → Fin 2 → ℝ) (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {v : Ω × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) |
      (a v.1,b v.1) = v.2} :=
  measurableSet_eq_fun ((ha.prodMk hb).comp measurable_fst) measurable_snd

end PaperI
