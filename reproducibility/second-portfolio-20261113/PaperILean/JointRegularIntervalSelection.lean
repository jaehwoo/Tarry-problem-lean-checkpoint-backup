import PaperILean.JointVariableIntervalCuts
import PaperILean.JointProjectedArcGraphs

/-! The original finite cut relation supplies a long consecutive regular
interval. One CAD selector is fixed on the joint relation before Borel
substitution; no arbitrary pointwise witnesses are declared measurable. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def zeroTotalizedVectorRelation {α β : Type*} (R : Set ((α ⊕ β) → ℝ)) :
    Set ((α ⊕ β) → ℝ) :=
  R ∪ {v | v ∘ Sum.inl ∉ projectionDomain R ∧ ∀ j, v (Sum.inr j)=0}

theorem zeroTotalizedVectorRelation_definable {α β : Type} [Finite α] [Fintype β]
    {R : Set ((α ⊕ β) → ℝ)} (hR : (univ : Set ℝ).Definable Language.ring R) :
    (univ : Set ℝ).Definable Language.ring (zeroTotalizedVectorRelation R) := by
  have hD := (realDefinable_exists hR).compl.preimage_comp (Sum.inl : α → α ⊕ β)
  have h0 := realDefinable_finite_all (fun j : β => realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inr j : α ⊕ β)))
  exact hR.union (hD.inter (by simpa using h0))

theorem published_joint_vector_selector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α β : Type} [Finite α] [Finite β] (R : Set ((α ⊕ β) → ℝ))
    (hR : (univ : Set ℝ).Definable Language.ring R) :
    ∃ F : (α → ℝ) → β → ℝ, Measurable F ∧
      HasPolynomialSignDescription (selectedFunctionGraph univ F) ∧
      ∀ p∈projectionDomain R, Sum.elim p (F p) ∈ R := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  have hne (p : α → ℝ) : ∃ x, Sum.elim p x ∈ zeroTotalizedVectorRelation R := by
    by_cases hp : p∈projectionDomain R
    · obtain ⟨x,hx⟩ := hp
      exact ⟨x,Or.inl hx⟩
    · exact ⟨fun _ => 0,Or.inr ⟨hp,fun _ => rfl⟩⟩
  obtain ⟨F,hF,hmem⟩ := published_cylindrical_selector hCAD hQE univ
    (zeroTotalizedVectorRelation R) ⟨∅,polynomialSignDetermined_univ⟩
    (hQE.finite_sign_description _ (zeroTotalizedVectorRelation_definable hR)) (fun p _ => hne p)
  have hm := published_measurable_selected_function hQE hHardt univ F
    (hasPolynomialSignDescription_definable hF)
  have he : Measurable (fun p : α → ℝ => (⟨p,mem_univ p⟩ : (univ : Set (α → ℝ)))) :=
    measurable_id.subtype_mk
  refine ⟨F,hm.comp he,hF,?_⟩
  intro p hp
  rcases hmem p (mem_univ p) with h | h
  · exact h
  · exact (h.1 hp).elim

def cutGapRelation {α : Type*} (C : Set ((α ⊕ Unit) → ℝ)) : Set ((α ⊕ Fin 2) → ℝ) :=
  {v | v (Sum.inr 0) ∈ scalarProjectionFiber C (v ∘ Sum.inl) ∧
    v (Sum.inr 1) ∈ scalarProjectionFiber C (v ∘ Sum.inl) ∧
    v (Sum.inr 0)<v (Sum.inr 1) ∧
    ∀ c∈scalarProjectionFiber C (v ∘ Sum.inl), c∉Ioo (v (Sum.inr 0)) (v (Sum.inr 1))}

theorem cutGapRelation_definable {α : Type} [Finite α]
    {C : Set ((α ⊕ Unit) → ℝ)} (hC : (univ : Set ℝ).Definable Language.ring C) :
    (univ : Set ℝ).Definable Language.ring (cutGapRelation C) := by
  let B := α ⊕ Fin 2
  let e : α ⊕ Unit → B ⊕ Unit := Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  have hm0 := hC.preimage_comp (Sum.map id (fun _ : Unit => (0 : Fin 2)))
  have hm1 := hC.preimage_comp (Sum.map id (fun _ : Unit => (1 : Fin 2)))
  have hlt := realCoordinate_lt_definable (Sum.inr (0 : Fin 2) : B) (Sum.inr 1)
  have hinside := (realCoordinate_lt_definable (Sum.inl (Sum.inr 0) : B ⊕ Unit) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr () : B ⊕ Unit) (Sum.inl (Sum.inr 1)))
  have hAll := realDefinable_forall ((hC.preimage_comp e).compl.union hinside.compl)
  have hgap : (univ : Set ℝ).Definable Language.ring
      {v : B → ℝ | ∀ c∈scalarProjectionFiber C (v ∘ Sum.inl), c∉Ioo (v (Sum.inr 0)) (v (Sum.inr 1))} := by
    convert hAll using 1
    ext v
    have he (x : Unit → ℝ) : Sum.elim v x ∘ e = Sum.elim (v ∘ Sum.inl) (fun _ => x ()) := by
      funext z; cases z <;> rfl
    simp only [mem_setOf_eq,mem_union,mem_compl_iff,mem_preimage,mem_inter_iff,
      he,Sum.elim_inl,Sum.elim_inr]
    constructor
    · intro h x
      by_cases hx : x ()∈scalarProjectionFiber C (v ∘ Sum.inl)
      · exact Or.inr (h (x ()) hx)
      · exact Or.inl hx
    · intro h x hx
      exact (h (fun _ => x)).resolve_left (not_not.mpr hx)
  convert hm0.inter (hm1.inter (hlt.inter hgap)) using 1
  ext v
  have he (j : Fin 2) : v ∘ Sum.map id (fun _ : Unit => j) = Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr j)) := by
    funext z; cases z <;> rfl
  simp only [cutGapRelation,scalarProjectionFiber,mem_setOf_eq,mem_inter_iff,mem_preimage,he]
  rfl

def longOriginalRegularIntervalRelation {α : Type*}
    (C : Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ)) (K : ℕ) :
    Set (((α ⊕ Fin 2) ⊕ Fin 2) → ℝ) :=
  {v | v∈cutGapRelation C ∧
    v (Sum.inl (Sum.inr 1))-v (Sum.inl (Sum.inr 0)) ≤
      ((K : ℝ)+1)*(v (Sum.inr 1)-v (Sum.inr 0))}

theorem longOriginalRegularIntervalRelation_definable {α : Type} [Finite α]
    {C : Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ)}
    (hC : (univ : Set ℝ).Definable Language.ring C) (K : ℕ) :
    (univ : Set ℝ).Definable Language.ring (longOriginalRegularIntervalRelation C K) := by
  have h := realPolynomial_le_definable
    (MvPolynomial.X (Sum.inl (Sum.inr 1) : (α ⊕ Fin 2) ⊕ Fin 2)-MvPolynomial.X (Sum.inl (Sum.inr 0)))
    (MvPolynomial.C ((K : ℝ)+1)*(MvPolynomial.X (Sum.inr 1)-MvPolynomial.X (Sum.inr 0)))
  exact (cutGapRelation_definable hC).inter (by
    simpa only [map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X] using h)

theorem JointOriginalIntervalCutFamily.long_gap {α : Type*}
    {G : Set ((α ⊕ Fin 2) → ℝ)} {C : Set (((α ⊕ Fin 2) ⊕ Unit) → ℝ)} {K : ℕ}
    (h : JointOriginalIntervalCutFamily G C K) (p : α → ℝ) {a b : ℝ} (hab : a<b) :
    Sum.elim p ![a,b]∈projectionDomain (longOriginalRegularIntervalRelation C K) := by
  have hp := h p a b hab.le
  have hc : hp.1.toFinset.card ≤ K := by simpa only [Nat.card_eq_card_finite_toFinset hp.1] using hp.2.1
  obtain ⟨u,hu,v,hv,huv,hlen,hgap⟩ := exists_long_consecutive_cut_interval hp.1.toFinset hab
    (hp.1.mem_toFinset.mpr hp.2.2.1) (hp.1.mem_toFinset.mpr hp.2.2.2.1)
    (fun x hx => hp.2.2.2.2.1 (hp.1.mem_toFinset.mp hx)) hc
  refine ⟨![u,v],⟨hp.1.mem_toFinset.mp hu,hp.1.mem_toFinset.mp hv,huv,
    fun c hc => hgap c (hp.1.mem_toFinset.mpr hc)⟩,?_⟩
  change b-a ≤ ((K : ℝ)+1)*(v-u)
  exact (div_le_iff₀ (show 0<(K : ℝ)+1 by positivity)).mp hlen |>.trans_eq (by ring)

/-- A fixed joint graph yields joint regular endpoints and one common loss
before every represented function and positive interval. -/
theorem published_joint_original_regular_interval
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] (G : Set ((α ⊕ Fin 2) → ℝ))
    (hG : (univ : Set ℝ).Definable Language.ring G) :
    ∃ (K : ℕ) (E : ((α ⊕ Fin 2) → ℝ) → Fin 2 → ℝ), 0<K ∧ Measurable E ∧
      HasPolynomialSignDescription (selectedFunctionGraph univ E) ∧
      ∀ (p : α → ℝ) (f : ℝ → ℝ) (a b : ℝ), a<b →
      (∀ x∈Icc a b, ∀ y, Sum.elim p ![x,y]∈G ↔ y=f x) →
      let e := E (Sum.elim p ![a,b])
      a≤e 0 ∧ e 0<e 1 ∧ e 1≤b ∧ (b-a)/(K : ℝ)≤e 1-e 0 ∧
        AnalyticOnNhd ℝ f (Ioo (e 0) (e 1)) ∧ DerivativeSignOn f (Ioo (e 0) (e 1)) := by
  obtain ⟨C,K,hC,hcuts⟩ := published_joint_original_interval_cut_family hCell hHardt hQE hPiece G hG
  obtain ⟨E,hEm,hEs,hER⟩ := published_joint_vector_selector hCAD hQE hHardt
    (longOriginalRegularIntervalRelation C K)
    (longOriginalRegularIntervalRelation_definable (hasPolynomialSignDescription_definable hC) K)
  refine ⟨K+1,E,Nat.succ_pos K,hEm,hEs,?_⟩
  intro p f a b hab hrep
  have hp := hcuts p a b hab.le
  have he := hER _ (hcuts.long_gap p hab)
  obtain ⟨hu,hv,huv,hgap⟩ := he.1
  have hA := hp.2.2.2.2.2 f hrep _ hu _ hv huv hgap
  refine ⟨(hp.2.2.2.2.1 hu).1,huv,(hp.2.2.2.2.1 hv).2,?_,hA⟩
  rw [Nat.cast_add,Nat.cast_one]
  exact (div_le_iff₀ (by positivity : 0<(K : ℝ)+1)).mpr (by simpa only [mul_comm] using he.2)

end PaperI
