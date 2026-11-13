import PaperILean.JointPlanarConeTests

/-! Original I1263/I1265: the graph over the SAME signed coordinate on the
SAME closed subarc. Pauses need no unique time inverse. Zero totalization is
only outside the projection domain; no value on the actual arc is changed. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def zeroTotalizedScalarRelation {α : Type*} (R : Set ((α ⊕ Unit) → ℝ)) :
    Set ((α ⊕ Unit) → ℝ) :=
  R ∪ {v | v ∘ Sum.inl ∉ projectionDomain R ∧ v (Sum.inr ())=0}

theorem zeroTotalizedScalarRelation_definable {α : Type} [Finite α]
    {R : Set ((α ⊕ Unit) → ℝ)}
    (hR : (univ : Set ℝ).Definable Language.ring R) :
    (univ : Set ℝ).Definable Language.ring (zeroTotalizedScalarRelation R) := by
  have hD := (realDefinable_exists hR).compl.preimage_comp (Sum.inl : α → α ⊕ Unit)
  have h0 := realPolynomial_zero_definable (MvPolynomial.X (Sum.inr () : α ⊕ Unit))
  exact hR.union (hD.inter (by simpa using h0))

theorem zeroTotalizedScalarRelation_nonempty {α : Type*}
    (R : Set ((α ⊕ Unit) → ℝ)) (p : α → ℝ) :
    ∃ x, Sum.elim p x ∈ zeroTotalizedScalarRelation R := by
  classical
  by_cases hp : p∈projectionDomain R
  · obtain ⟨x,hx⟩ := hp
    exact ⟨x,Or.inl hx⟩
  · exact ⟨fun _ => 0,Or.inr ⟨hp,rfl⟩⟩

theorem published_joint_scalar_selector
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] (R : Set ((α ⊕ Unit) → ℝ))
    (hR : (univ : Set ℝ).Definable Language.ring R) :
    ∃ F : (α → ℝ) → ℝ, Measurable F ∧
      HasPolynomialSignDescription (selectedFunctionGraph univ (fun p (_ : Unit) => F p)) ∧
      ∀ p∈projectionDomain R, Sum.elim p (fun _ => F p) ∈ R := by
  letI : Fintype α := Fintype.ofFinite α
  obtain ⟨f,hf,hm⟩ := published_cylindrical_selector hCAD hQE univ
    (zeroTotalizedScalarRelation R) (hQE.finite_sign_description _ Set.definable_univ)
    (hQE.finite_sign_description _ (zeroTotalizedScalarRelation_definable hR))
    (fun p _ => zeroTotalizedScalarRelation_nonempty R p)
  have hfun : (fun p (_ : Unit) => f p ())=f := by funext p u; cases u; rfl
  have hmeas := published_measurable_selected_function hQE hHardt univ f
    (hasPolynomialSignDescription_definable hf)
  have he : Measurable (fun p : α → ℝ => (⟨p,mem_univ p⟩ : (univ : Set (α → ℝ)))) :=
    measurable_id.subtype_mk
  have hmglob : Measurable f := hmeas.comp he
  refine ⟨fun p => f p (), (measurable_pi_apply ()).comp hmglob, ?_, ?_⟩
  · simpa only [hfun] using hf
  · intro p hp
    have h := hm p (mem_univ p)
    rcases h with h | h
    · simpa only [congrFun hfun p] using h
    · exact (h.1 hp).elim

def jointProjectedArcRelation {α : Type*} (P : Set (α → ℝ))
    (g : (α → ℝ) → ℝ → Fin 2 → ℝ) (i k : Fin 2) (σ : ℝ) :
    Set (((α ⊕ Fin 3) ⊕ Unit) → ℝ) :=
  {v | ∃ z : Fin 3 → ℝ,
    Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
      (Sum.elim (fun _ : Unit => z 0) (fun j : Fin 2 => z j.succ)) ∈ jointUnitPathGraph P g ∧
    v (Sum.inl (Sum.inr 0)) ≤ z 0 ∧ z 0 ≤ v (Sum.inl (Sum.inr 1)) ∧
    v (Sum.inl (Sum.inr 2))=σ*z i.succ ∧ v (Sum.inr ())=z k.succ}

theorem jointProjectedArcRelation_definable {α : Type} [Finite α]
    {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    (i k : Fin 2) (σ : ℝ) :
    (univ : Set ℝ).Definable Language.ring (jointProjectedArcRelation P g i k σ) := by
  let E := ((α ⊕ Fin 3) ⊕ Unit) ⊕ Fin 3
  let e : α ⊕ (Unit ⊕ Fin 2) → E :=
    Sum.elim (fun r => Sum.inl (Sum.inl (Sum.inl r)))
      (Sum.elim (fun _ => Sum.inr 0) (fun j => Sum.inr j.succ))
  have hG := (hasPolynomialSignDescription_definable hg).preimage_comp e
  have ha := realPolynomial_le_definable (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 0)) : E))
    (MvPolynomial.X (Sum.inr 0))
  have hb := realPolynomial_le_definable (MvPolynomial.X (Sum.inr 0 : E))
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 1))))
  have hq := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr 2)) : E) -
      MvPolynomial.C σ * MvPolynomial.X (Sum.inr i.succ))
  have hy := realPolynomial_zero_definable
    (MvPolynomial.X (Sum.inl (Sum.inr ()) : E) - MvPolynomial.X (Sum.inr k.succ))
  convert realDefinable_exists (hG.inter (ha.inter (hb.inter (hq.inter hy)))) using 1
  ext v
  change (∃ z : Fin 3 → ℝ, _) ↔ ∃ z : Fin 3 → ℝ, _
  apply exists_congr
  intro z
  have he : Sum.elim v z ∘ e = Sum.elim (fun r => v (Sum.inl (Sum.inl r)))
      (Sum.elim (fun _ : Unit => z 0) (fun j : Fin 2 => z j.succ)) := by
    funext r
    rcases r with r | (u | j) <;> rfl
  simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,he,map_sub,map_mul,
    MvPolynomial.eval_X,MvPolynomial.eval_C,Sum.elim_inl,Sum.elim_inr,sub_eq_zero]

theorem jointProjectedArcRelation_realize {α : Type*}
    (P : Set (α → ℝ)) (g : (α → ℝ) → ℝ → Fin 2 → ℝ)
    {p : α → ℝ} (hp : p∈P) {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (i k : Fin 2) (σ q y : ℝ) :
    Sum.elim (Sum.elim p ![a,b,q]) (fun _ => y) ∈ jointProjectedArcRelation P g i k σ ↔
      ∃ t∈Icc a b, q=σ*g p t i ∧ y=g p t k := by
  constructor
  · rintro ⟨z,hz,hza,hzb,hq,hy⟩
    have hcoord : ∀ j : Fin 2, z j.succ=g p (z 0) j := fun j => congrFun hz.2.2 j
    exact ⟨z 0,⟨hza,hzb⟩,by simpa only [hcoord] using hq,by simpa only [hcoord] using hy⟩
  · rintro ⟨t,ht,hq,hy⟩
    refine ⟨![t,g p t 0,g p t 1],?_,ht.1,ht.2,?_,?_⟩
    · refine ⟨hp,⟨ha.1.trans ht.1,ht.2.trans hb.2⟩,?_⟩
      funext j
      fin_cases j <;> rfl
    · fin_cases i <;> simpa using hq
    · fin_cases k <;> simpa using hy

theorem published_joint_projected_arc_graph
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    (i k : Fin 2) (σ : ℝ) :
    ∃ F : ((α ⊕ Fin 3) → ℝ) → ℝ, Measurable F ∧
      HasPolynomialSignDescription (selectedFunctionGraph univ (fun p (_ : Unit) => F p)) ∧
      ∀ p∈P, ∀ a∈Icc (0:ℝ) 1, ∀ b∈Icc (0:ℝ) 1, a≤b →
        DirectedPlanarGraphArc (g p) a b i k σ →
        LipschitzOnWith 1 (fun q => F (Sum.elim p ![a,b,q]))
          (Icc (σ*g p a i) (σ*g p b i)) ∧
        (∀ t∈Icc a b, F (Sum.elim p ![a,b,σ*g p t i])=g p t k) ∧
        ∀ q∈Icc (σ*g p a i) (σ*g p b i),
          ∃ t∈Icc a b, q=σ*g p t i ∧ F (Sum.elim p ![a,b,q])=g p t k := by
  obtain ⟨F,hFm,hFs,hFR⟩ := published_joint_scalar_selector hCAD hQE hHardt
    (jointProjectedArcRelation P g i k σ) (jointProjectedArcRelation_definable hg i k σ)
  refine ⟨F,hFm,hFs,?_⟩
  intro p hp a ha b hb hab hArc
  obtain ⟨h,hLip,hEq,hOnto⟩ := hArc.2.2.2.2
  have hrange (t : ℝ) (ht : t∈Icc a b) : σ*g p t i∈Icc (σ*g p a i) (σ*g p b i) :=
    ⟨hArc.2.2.1 (left_mem_Icc.mpr hab) ht ht.1,
      hArc.2.2.1 ht (right_mem_Icc.mpr hab) ht.2⟩
  have hmem (q : ℝ) (hq : q∈Icc (σ*g p a i) (σ*g p b i)) :
      ∃ t∈Icc a b, q=σ*g p t i ∧ F (Sum.elim p ![a,b,q])=g p t k := by
    obtain ⟨t,ht,he⟩ := hOnto q hq
    have hD : Sum.elim p ![a,b,q] ∈ projectionDomain (jointProjectedArcRelation P g i k σ) :=
      ⟨fun _ => g p t k,(jointProjectedArcRelation_realize P g hp ha hb i k σ q _).mpr
        ⟨t,ht,he.symm,rfl⟩⟩
    exact (jointProjectedArcRelation_realize P g hp ha hb i k σ q _).mp (hFR _ hD)
  have hsame (q : ℝ) (hq : q∈Icc (σ*g p a i) (σ*g p b i)) :
      F (Sum.elim p ![a,b,q])=h q := by
    obtain ⟨t,ht,hq',hF⟩ := hmem q hq
    exact hF.trans (by rw [hq']; exact (hEq t ht).symm)
  refine ⟨?_,?_,hmem⟩
  · intro q hq r hr
    simpa only [hsame q hq,hsame r hr] using hLip hq hr
  · intro t ht
    exact (hsame _ (hrange t ht)).trans (hEq t ht)

end PaperI
