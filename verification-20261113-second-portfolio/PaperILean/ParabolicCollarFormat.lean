import PaperILean.ParabolicCollarGeometry
import PaperILean.BoundedQuantifiedFormat
import PaperILean.PolynomialSignPullbackDegree
import PaperILean.PublishedFiberFormatComponents
import PaperILean.RegularCoefficientFiberTopology

open Set Filter MvPolynomial

noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

/-- The source uses the original algebraic parameter, with four actual seed values. -/
def originalSeedGraph (a b : ℝ) (γ : ℝ → Plane) (d v : Plane → ℝ) :
    Set ((Unit ⊕ Fin 4) → ℝ) :=
  {w | w (Sum.inl ()) ∈ Ioo a b ∧
    (fun i => w (Sum.inr i)) =
      ![(γ (w (Sum.inl ()))).1,(γ (w (Sum.inl ()))).2,
        d (γ (w (Sum.inl ()))),v (γ (w (Sum.inl ())))]}

def collarDomain (a b w : ℝ) : Set Coordinates :=
  {x | x 0∈Ioo a b ∧ x 1∈Ioo (-w) w}

/-- Graph with output coordinates first, so each projection fiber is an actual input fiber. -/
def originalCollarGraph (a b w : ℝ) (γ : ℝ → Plane) (d v : Plane → ℝ) :
    Set ((Fin 2 ⊕ Fin 2) → ℝ) :=
  {x | (fun i => x (Sum.inr i))∈collarDomain a b w ∧
    collarMap γ d v (fun i => x (Sum.inr i))=(fun i => x (Sum.inl i))}

private abbrev Free := Fin 2 ⊕ Fin 2
private abbrev All := Free ⊕ Fin 4

private def seedSubstitution : (Unit ⊕ Fin 4) → MvPolynomial All ℝ
  | Sum.inl _ => X (Sum.inl (Sum.inr 0))
  | Sum.inr i => X (Sum.inr i)

private def τ : MvPolynomial All ℝ := X (Sum.inl (Sum.inr 1))

private def collarMatrix (G : Set ((Unit ⊕ Fin 4) → ℝ)) (w : ℝ) : Set (All → ℝ) :=
  {x | Sum.elim (fun _ => x (Sum.inl (Sum.inr 0))) (fun i => x (Sum.inr i))∈G ∧
    -w < x (Sum.inl (Sum.inr 1)) ∧ x (Sum.inl (Sum.inr 1)) < w ∧
    x (Sum.inr 0) + x (Sum.inr 2)*x (Sum.inl (Sum.inr 1)) +
      x (Sum.inr 3)*x (Sum.inl (Sum.inr 1))^2/2 = x (Sum.inl (Sum.inl 0)) ∧
    x (Sum.inr 1)+x (Sum.inl (Sum.inr 1))=x (Sum.inl (Sum.inl 1))}

private theorem collar_matrix_sign
    {G : Set ((Unit ⊕ Fin 4) → ℝ)} {A : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ)}
    {s D : ℕ} (hc : A.card≤s) (hd : ∀ p∈A,p.totalDegree≤D)
    (hG : PolynomialSignDetermined A G) (w : ℝ) :
    ∃ B : Finset (MvPolynomial All ℝ), B.card≤s+4 ∧
      (∀ p∈B, p.totalDegree≤max D 3) ∧ PolynomialSignDetermined B (collarMatrix G w) := by
  classical
  have hdeg (i : Unit ⊕ Fin 4) : (seedSubstitution i).totalDegree≤1 := by
    cases i <;> simp [seedSubstitution]
  obtain ⟨B,hB,hBD,hBS⟩ := polynomial_preimage_bounded_sign_format A G s D 1 hc hd hG _ hdeg
  let p₀ : MvPolynomial All ℝ := τ+C w
  let p₁ : MvPolynomial All ℝ := C w-τ
  let p₂ : MvPolynomial All ℝ := X (Sum.inr 0)+X (Sum.inr 2)*τ+
    X (Sum.inr 3)*τ^2*C (1/2)-X (Sum.inl (Sum.inl 0))
  let p₃ : MvPolynomial All ℝ := X (Sum.inr 1)+τ-X (Sum.inl (Sum.inl 1))
  have d₀ : p₀.totalDegree≤3 := (MvPolynomial.totalDegree_add ..).trans (by simp [τ])
  have d₁ : p₁.totalDegree≤3 := (MvPolynomial.totalDegree_sub ..).trans (by simp [τ])
  have d₂a : (X (Sum.inr 2) * τ).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul ..).trans (by simp [τ])
  have d₂b : (X (Sum.inr 3) * τ^2 * C (1/2)).totalDegree ≤ 3 := by
    have hpow := (MvPolynomial.totalDegree_pow τ 2).trans (by simp [τ] : 2*τ.totalDegree≤2)
    exact (MvPolynomial.totalDegree_mul ..).trans (by
      simp only [MvPolynomial.totalDegree_C,add_zero]
      exact (MvPolynomial.totalDegree_mul ..).trans (by simp; omega))
  have d₂ : p₂.totalDegree≤3 := (MvPolynomial.totalDegree_sub ..).trans (by
    apply max_le (MvPolynomial.totalDegree_add .. |>.trans _) (by simp)
    exact max_le ((MvPolynomial.totalDegree_add ..).trans (max_le (by simp) (d₂a.trans (by decide)))) d₂b)
  have d₃ : p₃.totalDegree≤3 := (MvPolynomial.totalDegree_sub ..).trans
    (max_le ((MvPolynomial.totalDegree_add ..).trans (by simp [τ])) (by simp))
  refine ⟨B∪{p₀,p₁,p₂,p₃}, (Finset.card_union_le ..).trans (add_le_add hB ?_),?_,?_⟩
  · exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right
      ((Finset.card_insert_le ..).trans (Nat.add_le_add_right
        ((Finset.card_insert_le ..).trans (by simp)) _)) _)
  · intro p hp
    rcases Finset.mem_union.mp hp with hb|hp
    · exact (show p.totalDegree≤D by simpa only [Nat.mul_one] using hBD p hb).trans
        (le_max_left D 3)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl
    all_goals exact (by assumption : _ ≤ 3).trans (le_max_right _ _)
  · intro x y h
    have hs := hBS x y fun p hp => h p (Finset.mem_union_left _ hp)
    have h₀ := h p₀ (Finset.mem_union_right _ (by simp))
    have h₁ := h p₁ (Finset.mem_union_right _ (by simp))
    have h₂ := h p₂ (Finset.mem_union_right _ (by simp))
    have h₃ := h p₃ (Finset.mem_union_right _ (by simp))
    change (fun i => eval x (seedSubstitution i))∈G ↔
      (fun i => eval y (seedSubstitution i))∈G at hs
    have he (z : All → ℝ) : (fun i => eval z (seedSubstitution i)) =
        Sum.elim (fun _ => z (Sum.inl (Sum.inr 0))) (fun i => z (Sum.inr i)) := by
      funext i
      cases i <;> simp [seedSubstitution]
    rw [he,he] at hs
    have hpos₀ := h₀.2
    have hpos₁ := h₁.2
    have heq₂ := h₂.1
    have heq₃ := h₃.1
    simp only [p₀,p₁,p₂,p₃,τ,map_add,map_sub,map_mul,map_pow,eval_X,eval_C,
      sub_eq_zero,sub_pos] at hpos₀ hpos₁ heq₂ heq₃
    have hfix (x y : ℝ) : 0 < x+y ↔ -y<x := by
      constructor <;> intro h <;> linarith
    simp only [hfix,mul_one_div] at hpos₀ heq₂
    exact and_congr hs (and_congr hpos₀ (and_congr hpos₁ (and_congr heq₂ heq₃)))

private theorem polynomial_sign_has_boolean_table {α : Type} (B : Finset (MvPolynomial α ℝ))
    (S : Set (α → ℝ)) (hS : PolynomialSignDetermined B S) :
    ∃ (p : Fin B.card → MvPolynomial α ℝ) (b : (Fin B.card → Bool × Bool) → Bool),
      (∀ i, p i∈B) ∧ polynomialBooleanSet p b = S := by
  classical
  let e := B.equivFin
  let p (i : Fin B.card) := (e.symm i).val
  let b (z : Fin B.card → Bool × Bool) := decide (∃ x∈S, polynomialFamilySignCode p x=z)
  refine ⟨p,b,fun i => (e.symm i).property,?_⟩
  ext x
  change b (polynomialFamilySignCode p x)=true ↔ x∈S
  simp only [b,decide_eq_true_eq]
  constructor
  · rintro ⟨y,hy,he⟩
    apply (hS y x ?_).mp hy
    intro q hq
    let i := e ⟨q,hq⟩
    have hq' : p i=q := by simp [p,i]
    have hi := congrFun he i
    simp only [polynomialFamilySignCode,hq'] at hi
    exact ⟨decide_eq_decide.mp (congrArg Prod.fst hi),
      decide_eq_decide.mp (congrArg Prod.snd hi)⟩
  · exact fun hx => ⟨x,hx,rfl⟩

private theorem collar_graph_projection (a b w : ℝ) (γ : ℝ → Plane) (d v : Plane → ℝ) :
    originalCollarGraph a b w γ d v =
      {x | ∃ y : Fin 4 → ℝ, Sum.elim x y∈collarMatrix (originalSeedGraph a b γ d v) w} := by
  ext x
  let s := x (Sum.inr 0)
  let t := x (Sum.inr 1)
  change ((s∈Ioo a b ∧ t∈Ioo (-w) w) ∧ _) ↔ _
  constructor
  · rintro ⟨⟨hs,ht⟩,hc⟩
    refine ⟨![(γ s).1,(γ s).2,d (γ s),v (γ s)],⟨hs,rfl⟩,ht.1,ht.2,?_,?_⟩
    · exact congrFun hc 0
    · exact congrFun hc 1
  · rintro ⟨y,⟨hs,hyeq⟩,ht₀,ht₁,hy,hz⟩
    have hval : y = ![(γ s).1,(γ s).2,d (γ s),v (γ s)] := hyeq
    subst y
    refine ⟨⟨hs,⟨ht₀,ht₁⟩⟩,?_⟩
    funext i
    fin_cases i
    · exact hy
    · exact hz

theorem collar_bounded_graph_format (hQE : PublishedQuantitativeRealQE) (s D : ℕ) :
    ∃ sOut DOut : ℕ,
      ∀ (a b w : ℝ) (γ : ℝ → Plane) (d v : Plane → ℝ)
        (A : Finset (MvPolynomial (Unit ⊕ Fin 4) ℝ)), A.card≤s →
        (∀ p∈A,p.totalDegree≤D) → PolynomialSignDetermined A (originalSeedGraph a b γ d v) →
        ∃ B : Finset (MvPolynomial Free ℝ), B.card≤sOut ∧
          (∀ p∈B,p.totalDegree≤DOut) ∧ PolynomialSignDetermined B (originalCollarGraph a b w γ d v) := by
  obtain ⟨sOut,DOut,hout⟩ := published_bounded_quantified_polynomial_sign_format hQE Free 1 4 (s+4) (max D 3)
  refine ⟨sOut,DOut,?_⟩
  intro a b w γ d v A hAc hAd hA
  obtain ⟨C,hC,hCd,hCs⟩ := collar_matrix_sign hAc hAd hA w
  obtain ⟨p,β,hp,ht⟩ := polynomial_sign_has_boolean_table C _ hCs
  let blocks : QuantifierPrefix := [(false,4)]
  obtain ⟨B,hB,hBd,hBs⟩ := hout blocks (by decide) (by decide) C.card hC p (fun i => hCd _ (hp i)) β
  refine ⟨B,hB,hBd,?_⟩
  have heq : polynomialPrenexSet blocks p β=originalCollarGraph a b w γ d v := by
    rw [collar_graph_projection]
    ext x
    change (∃ y : Fin 4 → ℝ, Sum.elim x (Fin.append y Fin.elim0) ∈ polynomialBooleanSet p β) ↔ _
    rw [ht]
    have he (y : Fin 4 → ℝ) : Fin.append y (Fin.elim0 : Fin 0 → ℝ)=y := by
      funext i
      have hi := Fin.append_left y (Fin.elim0 : Fin 0 → ℝ) i
      exact hi
    simp only [he]
    rfl
  exact heq ▸ hBs

/-- Uniform fiber bound using the actual continuous change from original to flux parameter. -/
theorem collar_uniform_fibers
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (s D : ℕ) :
    ∃ N : ℕ, ∀ (a b a' b' w : ℝ) (γ γ' : ℝ → Plane) (d v : Plane → ℝ)
      (r : ℝ → ℝ), ContinuousOn r (Ioo a' b') → BijOn r (Ioo a' b') (Ioo a b) →
      (∀ z∈Ioo a' b', γ (r z)=γ' z) →
      ∀ (A : Finset (MvPolynomial Free ℝ)), A.card≤s →
      (∀ p∈A,p.totalDegree≤D) → PolynomialSignDetermined A (originalCollarGraph a' b' w γ' d v) →
      (∀ x∈collarDomain a b w, ∃ L : Coordinates →L[ℝ] Coordinates,
        HasFDerivAt (collarMap γ d v) L x ∧ L.det≠0) →
      ∀ y : Coordinates, Finite {x | x∈collarDomain a b w ∧ collarMap γ d v x=y} ∧
        Nat.card {x | x∈collarDomain a b w ∧ collarMap γ d v x=y} ≤ N := by
  obtain ⟨N,hN⟩ := published_at_most_sign_format_totallyDisconnected_fiber_card_bound hCell hHardt hQE 2 s D
  refine ⟨N,?_⟩
  intro a b a' b' w γ γ' d v r hr hb hγ A hAc hAd hA hreg y
  let S := {x | x∈collarDomain a b w ∧ collarMap γ d v x=y}
  let G := originalCollarGraph a' b' w γ' d v
  let S' := projectionFiber G y
  have hS' (x : Coordinates) : x∈S' ↔ x∈collarDomain a' b' w ∧ collarMap γ' d v x=y := by
    rfl
  haveI : DiscreteTopology S := discrete_regularCoefficientFiber_of_det_ne_zero _ _ _ hreg
  let f : S' → S := fun x => ⟨![r (x.val 0),x.val 1],by
    have hx := (hS' x.val).mp x.property
    refine ⟨⟨hb.mapsTo hx.1.1,hx.1.2⟩,?_⟩
    rw [← hx.2]
    funext i
    fin_cases i <;> simp [collarMap,hγ _ hx.1.1]⟩
  have hi : Function.Injective f := by
    intro x z hxz
    have h₀ := congrArg (fun a : S => a.val 0) hxz
    have h₁ := congrArg (fun a : S => a.val 1) hxz
    have e₀ : x.val 0=z.val 0 := hb.injOn ((hS' _).mp x.property).1.1
      ((hS' _).mp z.property).1.1 h₀
    apply Subtype.ext
    funext i
    fin_cases i
    · exact e₀
    · exact h₁
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨z,hz,hzx⟩ := hb.surjOn x.property.1.1
    refine ⟨⟨![z,x.val 1],(hS' _).mpr ⟨⟨hz,x.property.1.2⟩,?_⟩⟩,?_⟩
    · rw [← x.property.2]
      funext i
      fin_cases i <;> simp [collarMap,← hzx,hγ z hz]
    · apply Subtype.ext
      funext i
      fin_cases i
      · exact hzx
      · rfl
  have hcf : Continuous f := by
    let x₀ : S' → Ioo a' b' := fun x => ⟨x.val 0,((hS' _).mp x.property).1.1⟩
    have hx₀ : Continuous x₀ := ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
    have hrx := (continuousOn_iff_continuous_restrict.mp hr).comp hx₀
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact hrx
    · change Continuous (fun z : S' => z.val 1)
      exact (continuous_apply (1 : Fin 2)).comp continuous_subtype_val
  haveI : DiscreteTopology S' := DiscreteTopology.of_continuous_injective hcf hi
  haveI : TotallyDisconnectedSpace S' := inferInstance
  obtain ⟨hf,hcard⟩ := hN 2 le_rfl (Fin 2) A G hAc hAd hA y inferInstance
  letI : Finite S' := hf
  let e : S' ≃ S := Equiv.ofBijective f ⟨hi,hs⟩
  exact ⟨Finite.of_injective e.symm e.symm.injective,
    (Nat.card_le_card_of_injective e.symm e.symm.injective).trans hcard⟩

end PaperI.ParabolicCollar
