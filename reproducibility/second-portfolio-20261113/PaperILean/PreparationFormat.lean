import PaperILean.OriginalPreparationSuperlevels
import PaperILean.PreparationMixedJets

/-! Uniform component bounds for the actual positive mixed-jet graphs.
The finite syntax family is fixed before the bound. All coefficient, branch,
interval, section, threshold and sign data remain parameters. -/

noncomputable section
namespace PaperI.Preparation
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def ComponentBound (K : ℕ) (S : Set ℝ) : Prop :=
  Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ K

def sectionPoint (axis : Bool) (fixed t : ℝ) : ℝ × ℝ :=
  if axis then (t, fixed) else (fixed, t)

def signedFieldSection (g : ℝ × ℝ → ℝ) (axis : Bool)
    (fixed l r threshold sign : ℝ) : Set ℝ :=
  {t | t ∈ Ioo l r ∧ threshold < sign * g (sectionPoint axis fixed t)}

def strictFieldSection {κ : Type} (g : κ → ℝ × ℝ → ℝ)
    (x l r : ℝ) (T : κ → ℝ) (active : κ → Bool) : Set ℝ :=
  {y | y ∈ Ioo l r ∧ ∀ k, active k = true → |g k (x, y)| < T k}

def fieldSuperlevelRelation {α : Type} (G : Set ((α ⊕ Fin 3) → ℝ))
    (axis : Bool) : Set (((α ⊕ Fin 5) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr 0))) (v (Sum.inl (Sum.inr 1))) ∧
    ∃ z : Unit → ℝ,
      Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
        ![(sectionPoint axis (v (Sum.inl (Sum.inr 2))) (v (Sum.inr ()))).1,
          (sectionPoint axis (v (Sum.inl (Sum.inr 2))) (v (Sum.inr ()))).2, z ()] ∈ G ∧
      v (Sum.inl (Sum.inr 3)) < v (Sum.inl (Sum.inr 4)) * z ()}

theorem fieldSuperlevelRelation_definable {α : Type} [Finite α]
    {G : Set ((α ⊕ Fin 3) → ℝ)}
    (hG : (univ : Set ℝ).Definable Language.ring G) (axis : Bool) :
    (univ : Set ℝ).Definable Language.ring (fieldSuperlevelRelation G axis) := by
  let β := (α ⊕ Fin 5) ⊕ Unit
  let e : α ⊕ Fin 3 → β ⊕ Unit := Sum.elim
    (fun c => Sum.inl (Sum.inl (Sum.inl c)))
    (fun j => if j = 0 then
        if axis then Sum.inl (Sum.inr ()) else Sum.inl (Sum.inl (Sum.inr 2))
      else if j = 1 then
        if axis then Sum.inl (Sum.inl (Sum.inr 2)) else Sum.inl (Sum.inr ())
      else Sum.inr ())
  have hvalue := realDefinable_exists ((hG.preimage_comp e).inter
    (realPolynomial_lt_definable
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 3))) : MvPolynomial (β ⊕ Unit) ℝ)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 4))) * MvPolynomial.X (Sum.inr ()))))
  have h := ((realCoordinate_lt_definable (Sum.inl (Sum.inr 0)) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr 1)))).inter hvalue
  convert h using 1
  ext v
  have he (z : Unit → ℝ) : Sum.elim v z ∘ e =
      Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
        ![(sectionPoint axis (v (Sum.inl (Sum.inr 2))) (v (Sum.inr ()))).1,
          (sectionPoint axis (v (Sum.inl (Sum.inr 2))) (v (Sum.inr ()))).2, z ()] := by
    funext j
    rcases j with c | j
    · rfl
    · fin_cases j <;> cases axis <;> rfl
  simp only [fieldSuperlevelRelation, mem_setOf_eq, mem_inter_iff, mem_Ioo,
    mem_preimage, he, MvPolynomial.eval_X, map_mul, Sum.elim_inl, Sum.elim_inr]
  apply and_congr_right
  intro _
  apply exists_congr
  intro z
  rw [he]

theorem fieldSuperlevelRelation_realize {α : Type}
    (G : Set ((α ⊕ Fin 3) → ℝ)) (p : α → ℝ) (g : ℝ × ℝ → ℝ)
    (axis : Bool) (fixed l r threshold sign : ℝ)
    (hrep : ∀ t ∈ Ioo l r, ∀ z : ℝ,
      Sum.elim p ![(sectionPoint axis fixed t).1, (sectionPoint axis fixed t).2,z] ∈ G ↔
        z = g (sectionPoint axis fixed t)) :
    scalarProjectionFiber (fieldSuperlevelRelation G axis)
      (Sum.elim p ![l,r,fixed,threshold,sign]) =
        signedFieldSection g axis fixed l r threshold sign := by
  ext t
  change (t ∈ Ioo l r ∧ ∃ z : Unit → ℝ, _ ∧ threshold < sign * z ()) ↔
    (t ∈ Ioo l r ∧ threshold < sign * g (sectionPoint axis fixed t))
  apply and_congr_right
  intro ht
  constructor
  · rintro ⟨z,hz,h⟩
    simpa only [(hrep t ht (z ())).mp hz] using h
  · intro h
    exact ⟨fun _ => g (sectionPoint axis fixed t), (hrep t ht _).mpr rfl, h⟩

def fieldGoodRelation {α κ : Type} (G : κ → Set ((α ⊕ Fin 3) → ℝ))
    (active : κ → Bool) : Set (((α ⊕ (Fin 3 ⊕ κ)) ⊕ Unit) → ℝ) :=
  {v | v (Sum.inr ()) ∈ Ioo (v (Sum.inl (Sum.inr (Sum.inl 0))))
      (v (Sum.inl (Sum.inr (Sum.inl 1)))) ∧
    ∀ k, active k = true → ∃ z : Unit → ℝ,
      Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
        ![v (Sum.inl (Sum.inr (Sum.inl 2))), v (Sum.inr ()),z ()] ∈ G k ∧
      -v (Sum.inl (Sum.inr (Sum.inr k))) < z () ∧
        z () < v (Sum.inl (Sum.inr (Sum.inr k)))}

theorem fieldGoodRelation_definable {α κ : Type} [Finite α] [Fintype κ]
    {G : κ → Set ((α ⊕ Fin 3) → ℝ)}
    (hG : ∀ k, (univ : Set ℝ).Definable Language.ring (G k)) (active : κ → Bool) :
    (univ : Set ℝ).Definable Language.ring (fieldGoodRelation G active) := by
  let β := (α ⊕ (Fin 3 ⊕ κ)) ⊕ Unit
  let e : α ⊕ Fin 3 → β ⊕ Unit := Sum.elim
    (fun c => Sum.inl (Sum.inl (Sum.inl c)))
    (fun j => if j = 0 then Sum.inl (Sum.inl (Sum.inr (Sum.inl 2)))
      else if j = 1 then Sum.inl (Sum.inr ()) else Sum.inr ())
  have hvalue (k : κ) : (univ : Set ℝ).Definable Language.ring
      {v : β → ℝ | ∃ z : Unit → ℝ,
        Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
          ![v (Sum.inl (Sum.inr (Sum.inl 2))),v (Sum.inr ()),z ()] ∈ G k ∧
        -v (Sum.inl (Sum.inr (Sum.inr k))) < z () ∧
          z () < v (Sum.inl (Sum.inr (Sum.inr k)))} := by
    let q : MvPolynomial (β ⊕ Unit) ℝ :=
      MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (Sum.inr k))))
    let z : MvPolynomial (β ⊕ Unit) ℝ := MvPolynomial.X (Sum.inr ())
    have h := realDefinable_exists (((hG k).preimage_comp e).inter
      ((realPolynomial_lt_definable (-q) z).inter (realPolynomial_lt_definable z q)))
    convert h using 1
    ext v
    have he (w : Unit → ℝ) : Sum.elim v w ∘ e =
        Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
          ![v (Sum.inl (Sum.inr (Sum.inl 2))),v (Sum.inr ()),w ()] := by
      funext j
      rcases j with c | j
      · rfl
      · fin_cases j <;> rfl
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, he, q, z,
      map_neg, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  have hmasked (k : κ) : (univ : Set ℝ).Definable Language.ring
      {v : β → ℝ | active k = true → ∃ z : Unit → ℝ,
        Sum.elim (fun c => v (Sum.inl (Sum.inl c)))
          ![v (Sum.inl (Sum.inr (Sum.inl 2))),v (Sum.inr ()),z ()] ∈ G k ∧
        -v (Sum.inl (Sum.inr (Sum.inr k))) < z () ∧
          z () < v (Sum.inl (Sum.inr (Sum.inr k)))} := by
    by_cases hk : active k = true
    · simpa only [hk, true_implies] using hvalue k
    · simp [hk]
  exact ((realCoordinate_lt_definable (Sum.inl (Sum.inr (Sum.inl 0))) (Sum.inr ())).inter
    (realCoordinate_lt_definable (Sum.inr ()) (Sum.inl (Sum.inr (Sum.inl 1))))).inter
      (realDefinable_finite_all hmasked)

theorem fieldGoodRelation_realize {α κ : Type}
    (G : κ → Set ((α ⊕ Fin 3) → ℝ)) (p : α → ℝ) (g : κ → ℝ × ℝ → ℝ)
    (x l r : ℝ) (T : κ → ℝ) (active : κ → Bool)
    (hrep : ∀ k, ∀ y ∈ Ioo l r, ∀ z : ℝ,
      Sum.elim p ![x,y,z] ∈ G k ↔ z = g k (x,y)) :
    scalarProjectionFiber (fieldGoodRelation G active)
      (Sum.elim p (Sum.elim ![l,r,x] T)) = strictFieldSection g x l r T active := by
  ext y
  change (y ∈ Ioo l r ∧ ∀ k, active k = true → ∃ z : Unit → ℝ, _ ∧
    -T k < z () ∧ z () < T k) ↔ (y ∈ Ioo l r ∧ ∀ k, active k = true → _)
  apply and_congr_right
  intro hy
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  constructor
  · rintro ⟨z,hz,hlo,hhi⟩
    have he := (hrep k y hy (z ())).mp hz
    exact abs_lt.mpr (he ▸ ⟨hlo,hhi⟩)
  · intro h
    exact ⟨fun _ => g k (x,y), (hrep k y hy _).mpr rfl,
      (abs_lt.mp h).1, (abs_lt.mp h).2⟩

theorem published_uniform_field_section_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α κ : Type} [Finite α] [Fintype κ]
    (G : κ → Set ((α ⊕ Fin 3) → ℝ))
    (hG : ∀ k, (univ : Set ℝ).Definable Language.ring (G k)) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (g : κ → ℝ × ℝ → ℝ) (x0 x1 y0 y1 : ℝ),
      (∀ k, ∀ q ∈ Ioo x0 x1 ×ˢ Ioo y0 y1, ∀ z : ℝ,
        Sum.elim p ![q.1,q.2,z] ∈ G k ↔ z = g k q) →
      (∀ k axis fixed l r threshold sign,
        (∀ t ∈ Ioo l r, sectionPoint axis fixed t ∈ Ioo x0 x1 ×ˢ Ioo y0 y1) →
        ComponentBound K (signedFieldSection (g k) axis fixed l r threshold sign)) ∧
      (∀ x ∈ Ioo x0 x1, ∀ l r, Ioo l r ⊆ Ioo y0 y1 → ∀ T active,
        ComponentBound K (strictFieldSection g x l r T active)) := by
  obtain ⟨KS,hKS⟩ := published_finite_family_projection_fiber_component_bound
    hCell hHardt hQE (fun q : κ × Bool => fieldSuperlevelRelation (G q.1) q.2)
    (fun q => hQE.finite_sign_description _ (fieldSuperlevelRelation_definable (hG q.1) q.2))
  obtain ⟨KH,hKH⟩ := published_finite_family_projection_fiber_component_bound
    hCell hHardt hQE (fun active : κ → Bool => fieldGoodRelation G active)
    (fun active => hQE.finite_sign_description _ (fieldGoodRelation_definable hG active))
  refine ⟨max KS KH, ?_⟩
  intro p g x0 x1 y0 y1 hrep
  constructor
  · intro k axis fixed l r threshold sign hsection
    have hb := finite_connectedComponents_and_card_le_of_homeomorph
      (projectionFiberUnitHomeomorphScalar (fieldSuperlevelRelation (G k) axis)
        (Sum.elim p ![l,r,fixed,threshold,sign]))
      (hKS (k,axis) (Sum.elim p ![l,r,fixed,threshold,sign]))
    rw [fieldSuperlevelRelation_realize (G k) p (g k) axis fixed l r threshold sign
      (fun t ht z => hrep k _ (hsection t ht) z)] at hb
    exact ⟨hb.1, hb.2.trans (le_max_left _ _)⟩
  · intro x hx l r hsub T active
    have hb := finite_connectedComponents_and_card_le_of_homeomorph
      (projectionFiberUnitHomeomorphScalar (fieldGoodRelation G active)
        (Sum.elim p (Sum.elim ![l,r,x] T)))
      (hKH active (Sum.elim p (Sum.elim ![l,r,x] T)))
    rw [fieldGoodRelation_realize G p g x l r T active
      (fun k y hy z => hrep k (x,y) ⟨hx,hsub hy⟩ z)] at hb
    exact ⟨hb.1, hb.2.trans (le_max_right _ _)⟩

abbrev PositiveJetIndex (ι : Type) (N : ℕ) :=
  {q : ι × Fin (N + 1) × Fin (N + 1) //
    0 < q.2.1.val + q.2.2.val ∧ q.2.1.val + q.2.2.val ≤ N}

def positiveJet {ι : Type} {N : ℕ} (f : ι → ℝ × ℝ → ℝ)
    (q : PositiveJetIndex ι N) : ℝ × ℝ → ℝ :=
  mixedJet (f q.val.1) q.val.2.1.val q.val.2.2.val

def positiveHorizontalSection {ι : Type} (f : ι → ℝ × ℝ → ℝ)
    (N : ℕ) (x l r : ℝ) (T : ι → Fin (N + 1) → ℝ) (active : ι → Bool) : Set ℝ :=
  {y | y ∈ Ioo l r ∧ ∀ i (a : Fin (N + 1)), 0 < a.val → active i = true →
    |horizontalJet (f i) a.val (x,y)| < T i a}

theorem positiveHorizontalSection_eq_strictFieldSection
    {ι : Type} {N : ℕ} (f : ι → ℝ × ℝ → ℝ) (x l r : ℝ)
    (T : ι → Fin (N + 1) → ℝ) (active : ι → Bool) :
    positiveHorizontalSection f N x l r T active =
      strictFieldSection (positiveJet f) x l r
        (fun q => T q.val.1 q.val.2.1)
        (fun q => if q.val.2.2.val = 0 then active q.val.1 else false) := by
  ext y
  change (y ∈ Ioo l r ∧ ∀ i (a : Fin (N + 1)), 0 < a.val → active i = true → _) ↔
    (y ∈ Ioo l r ∧ ∀ q : PositiveJetIndex ι N,
      (if q.val.2.2.val = 0 then active q.val.1 else false) = true → _)
  apply and_congr_right
  intro _
  constructor
  · intro h q hactive
    have hz : q.val.2.2.val = 0 := by
      by_contra hz
      simp [hz] at hactive
    have hpos : 0 < q.val.2.1.val := by have hh := q.property.1; omega
    have ha : active q.val.1 = true := by simpa only [hz, if_true] using hactive
    simpa only [positiveJet, hz, mixedJet_zero_right] using h q.val.1 q.val.2.1 hpos ha
  · intro h i a ha hactive
    let q : PositiveJetIndex ι N :=
      ⟨(i,a,⟨0, Nat.zero_lt_succ N⟩), by
        simpa only [Nat.add_zero] using And.intro ha (Nat.lt_succ_iff.mp a.isLt)⟩
    have hq := h q (by simpa [q] using hactive)
    simpa only [positiveJet, q, mixedJet_zero_right] using hq

/-- The component hypotheses needed by the rectangle engine, derived from
only the positive actual mixed-jet graphs. No scalar zero-order graph occurs. -/
theorem published_uniform_positiveJet_components
    (hCell : PublishedFiniteConnectedCover)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    {α ι : Type} [Finite α] [Fintype ι] (N : ℕ)
    (G : PositiveJetIndex ι N → Set ((α ⊕ Fin 3) → ℝ))
    (hG : ∀ q, (univ : Set ℝ).Definable Language.ring (G q)) :
    ∃ K : ℕ, ∀ (p : α → ℝ) (f : ι → ℝ × ℝ → ℝ) (x0 x1 y0 y1 : ℝ),
      (∀ j, ∀ q ∈ Ioo x0 x1 ×ˢ Ioo y0 y1, ∀ z : ℝ,
        Sum.elim p ![q.1,q.2,z] ∈ G j ↔ z = positiveJet f j q) →
      (∀ i y, y ∈ Ioo y0 y1 → ∀ n, 0 < n → n ≤ N → ∀ threshold sign,
        ComponentBound K (signedIteratedDerivativeSuperlevel
          (fun x => f i (x,y)) n x0 x1 threshold sign)) ∧
      (∀ i x, x ∈ Ioo x0 x1 → ∀ a b, 0 < b → a + b ≤ N →
        ∀ l r, Ioo l r ⊆ Ioo y0 y1 → ∀ threshold sign,
          ComponentBound K (signedIteratedDerivativeSuperlevel
            (fun y => horizontalJet (f i) a (x,y)) b l r threshold sign)) ∧
      (∀ x, x ∈ Ioo x0 x1 → ∀ T active,
        ComponentBound K (positiveHorizontalSection f N x y0 y1 T active)) := by
  obtain ⟨K,hK⟩ := published_uniform_field_section_components hCell hHardt hQE G hG
  refine ⟨K, ?_⟩
  intro p f x0 x1 y0 y1 hrep
  obtain ⟨hS,hH⟩ := hK p (positiveJet f) x0 x1 y0 y1 hrep
  constructor
  · intro i y hy n hn hnN threshold sign
    let j : PositiveJetIndex ι N :=
      ⟨(i,⟨n,Nat.lt_succ_iff.mpr hnN⟩,⟨0,Nat.zero_lt_succ N⟩), by simpa using And.intro hn hnN⟩
    have hb := hS j true y x0 x1 threshold sign (fun t ht => ⟨ht,hy⟩)
    have he : signedFieldSection (positiveJet f j) true y x0 x1 threshold sign =
        signedIteratedDerivativeSuperlevel (fun x => f i (x,y)) n x0 x1 threshold sign := by
      ext t
      simp only [signedFieldSection, signedIteratedDerivativeSuperlevel, mem_setOf_eq,
        sectionPoint, Bool.true_eq, if_true, positiveJet, j, mixedJet_zero_right,
        horizontalJet_eq_iteratedDeriv]
    exact he ▸ hb
  constructor
  · intro i x hx a b hb hab l r hsub threshold sign
    let j : PositiveJetIndex ι N :=
      ⟨(i,⟨a,by omega⟩,⟨b,by omega⟩), by
        change 0 < a + b ∧ a + b ≤ N
        exact ⟨by omega,hab⟩⟩
    have hc := hS j false x l r threshold sign (fun t ht => ⟨hx,hsub ht⟩)
    have he : signedFieldSection (positiveJet f j) false x l r threshold sign =
        signedIteratedDerivativeSuperlevel
          (fun y => horizontalJet (f i) a (x,y)) b l r threshold sign := by
      ext t
      simp only [signedFieldSection, signedIteratedDerivativeSuperlevel, mem_setOf_eq,
        sectionPoint, Bool.false_eq_true, if_false, positiveJet, j, mixedJet_eq_iteratedDeriv]
    exact he ▸ hc
  · intro x hx T active
    rw [positiveHorizontalSection_eq_strictFieldSection]
    exact hH x hx y0 y1 Subset.rfl _ _

end PaperI.Preparation
