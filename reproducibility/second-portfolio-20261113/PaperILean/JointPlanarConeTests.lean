import PaperILean.JointOriginalReadoutCuts

/-! Original I1263/I1265: finite signed-coordinate tests on the WHOLE actual
interval, retaining a joint definable test before arbitrary Borel pullback.
Stationary points, diagonal ties and constant pieces are included. -/
noncomputable section
namespace PaperI
open Set FirstOrder
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
attribute [local instance] Classical.propDecidable

def planarDirectionI : Fin 4 → Fin 2 := ![0,0,1,1]
def planarDirectionK : Fin 4 → Fin 2 := ![1,1,0,0]
def planarDirectionSign : Fin 4 → ℝ := ![1,-1,1,-1]

theorem planarDirection_distinct (d : Fin 4) : planarDirectionI d ≠ planarDirectionK d := by
  fin_cases d <;> norm_num [planarDirectionI,planarDirectionK]

theorem planarDirection_sign (d : Fin 4) :
    planarDirectionSign d=1 ∨ planarDirectionSign d= -1 := by
  fin_cases d <;> norm_num [planarDirectionSign]

def PlanarDirectionCone (g : ℝ → Fin 2 → ℝ) (a b : ℝ) (d : Fin 4) : Prop :=
  ∀ t ∈ Ioo a b, |deriv (fun r => g r (planarDirectionK d)) t| ≤
    planarDirectionSign d * deriv (fun r => g r (planarDirectionI d)) t

theorem OriginalPlanarGraphArc.exists_direction {g : ℝ → Fin 2 → ℝ} {a b : ℝ}
    (h : OriginalPlanarGraphArc g a b) : ∃ d, PlanarDirectionCone g a b d := by
  obtain ⟨i,k,σ,hg,hcone⟩ := h
  have hik := hg.1
  rcases hg.2.1 with rfl | rfl
  · fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact ⟨0,by simpa [PlanarDirectionCone,planarDirectionI,planarDirectionK,planarDirectionSign] using hcone⟩
    · exact ⟨2,by simpa [PlanarDirectionCone,planarDirectionI,planarDirectionK,planarDirectionSign] using hcone⟩
    · exact (hik rfl).elim
  · fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact ⟨1,by simpa [PlanarDirectionCone,planarDirectionI,planarDirectionK,planarDirectionSign] using hcone⟩
    · exact ⟨3,by simpa [PlanarDirectionCone,planarDirectionI,planarDirectionK,planarDirectionSign] using hcone⟩
    · exact (hik rfl).elim

def firstPlanarDirection (Q : Fin 4 → Prop) : Fin 4 :=
  if Q 0 then 0 else if Q 1 then 1 else if Q 2 then 2 else 3

theorem firstPlanarDirection_spec (Q : Fin 4 → Prop) (hQ : ∃ d, Q d) :
    Q (firstPlanarDirection Q) ∧ ∀ d < firstPlanarDirection Q, ¬ Q d := by
  unfold firstPlanarDirection
  split_ifs with h0 h1 h2
  · exact ⟨h0,by intro d hd; omega⟩
  · refine ⟨h1,?_⟩
    intro d hd
    have : d=0 := by omega
    simpa [this] using h0
  · refine ⟨h2,?_⟩
    intro d hd
    fin_cases d <;> simp_all
  · have h3 : Q 3 := by obtain ⟨d,hd⟩ := hQ; fin_cases d <;> simp_all
    refine ⟨h3,?_⟩
    intro d hd
    fin_cases d <;> simp_all

theorem measurable_firstPlanarDirection {Ω : Type*} [MeasurableSpace Ω]
    (Q : Ω → Fin 4 → Prop) (hQ : ∀ d, MeasurableSet {p | Q p d}) :
    Measurable (fun p => firstPlanarDirection (Q p)) := by
  exact measurable_const.ite (hQ 0)
    (measurable_const.ite (hQ 1) (measurable_const.ite (hQ 2) measurable_const))

def jointGraphConeTest {α : Type*} (G : Fin 2 → Set ((α ⊕ Fin 2) → ℝ))
    (i k : Fin 2) (σ : ℝ) : Set ((α ⊕ Fin 2) → ℝ) :=
  {v | ∀ z : Fin 3 → ℝ,
    v (Sum.inr 0) < z 0 → z 0 < v (Sum.inr 1) →
    Sum.elim (v ∘ Sum.inl) ![z 0,z 1] ∈ graphDerivativeRelation (G 0) →
    Sum.elim (v ∘ Sum.inl) ![z 0,z 2] ∈ graphDerivativeRelation (G 1) →
    |z k.succ| ≤ σ*z i.succ}

theorem jointGraphConeTest_definable {α : Type} [Finite α]
    (G : Fin 2 → Set ((α ⊕ Fin 2) → ℝ))
    (hG : ∀ j, (univ : Set ℝ).Definable Language.ring (G j))
    (i k : Fin 2) (σ : ℝ) :
    (univ : Set ℝ).Definable Language.ring (jointGraphConeTest G i k σ) := by
  let B := α ⊕ Fin 2
  let E := B ⊕ Fin 3
  let e0 : α ⊕ Fin 2 → E := Sum.elim (fun a => Sum.inl (Sum.inl a))
    (fun j => if j=0 then Sum.inr 0 else Sum.inr 1)
  let e1 : α ⊕ Fin 2 → E := Sum.elim (fun a => Sum.inl (Sum.inl a))
    (fun j => if j=0 then Sum.inr 0 else Sum.inr 2)
  have ha := realPolynomial_lt_definable (MvPolynomial.X (Sum.inl (Sum.inr 0) : E))
    (MvPolynomial.X (Sum.inr 0))
  have hb := realPolynomial_lt_definable (MvPolynomial.X (Sum.inr 0 : E))
    (MvPolynomial.X (Sum.inl (Sum.inr 1)))
  have h0 := (graphDerivativeRelation_definable (hG 0)).preimage_comp e0
  have h1 := (graphDerivativeRelation_definable (hG 1)).preimage_comp e1
  have hlo := realPolynomial_le_definable
    (-(MvPolynomial.C σ * MvPolynomial.X (Sum.inr i.succ : E)))
    (MvPolynomial.X (Sum.inr k.succ))
  have hhi := realPolynomial_le_definable (MvPolynomial.X (Sum.inr k.succ : E))
    (MvPolynomial.C σ * MvPolynomial.X (Sum.inr i.succ))
  have h := realDefinable_forall (ha.compl.union
    (hb.compl.union (h0.compl.union (h1.compl.union (hlo.inter hhi)))))
  convert h using 1
  ext v
  have he0 (z : Fin 3 → ℝ) : Sum.elim v z ∘ e0 = Sum.elim (v ∘ Sum.inl) ![z 0,z 1] := by
    funext r
    rcases r with r | r
    · rfl
    · fin_cases r <;> simp [e0]
  have he1 (z : Fin 3 → ℝ) : Sum.elim v z ∘ e1 = Sum.elim (v ∘ Sum.inl) ![z 0,z 2] := by
    funext r
    rcases r with r | r
    · rfl
    · fin_cases r <;> simp [e1]
  simp only [jointGraphConeTest,mem_setOf_eq,mem_union,mem_compl_iff,mem_inter_iff,
    mem_preimage,he0,he1,map_mul,map_neg,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Sum.elim_inl,Sum.elim_inr,abs_le]
  change (∀ z : Fin 3 → ℝ, _ → _ → _ → _ → _) ↔ ∀ z : Fin 3 → ℝ, _ ∨ _ ∨ _ ∨ _ ∨ _
  apply forall_congr'
  intro z
  rw [he0 z,he1 z]
  tauto

theorem jointGraphConeTest_realize {α : Type*}
    (G : Fin 2 → Set ((α ⊕ Fin 2) → ℝ)) (p : α → ℝ) (g : ℝ → Fin 2 → ℝ)
    (hG : ∀ j t, t∈Icc (0:ℝ) 1 → ∀ y, Sum.elim p ![t,y] ∈ G j ↔ y=g t j)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hd : ∀ j, DifferentiableOn ℝ (fun t => g t j) (Ioo a b))
    (i k : Fin 2) (σ : ℝ) :
    Sum.elim p ![a,b] ∈ jointGraphConeTest G i k σ ↔
      ∀ t∈Ioo a b, |deriv (fun r => g r k) t| ≤ σ*deriv (fun r => g r i) t := by
  have hloc (t : ℝ) (ht : t∈Ioo a b) : t∈Ioo (0:ℝ) 1 :=
    ⟨ha.1.trans_lt ht.1,ht.2.trans_le hb.2⟩
  have hreal (j : Fin 2) (t m : ℝ) (ht : t∈Ioo a b) :=
    graphDerivativeRelation_realize_iff_on_interval (G j) p (fun r => g r j) 0 1 t m
      (hG j) (hloc t ht)
  constructor
  · intro h t ht
    have hder (j : Fin 2) := ((hd j t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    have hh := h ![t,deriv (fun r => g r 0) t,deriv (fun r => g r 1) t] ht.1 ht.2
      ((hreal 0 t _ ht).mpr (hder 0)) ((hreal 1 t _ ht).mpr (hder 1))
    fin_cases i <;> fin_cases k <;> simpa using hh
  · intro h z hza hzb hz0 hz1
    have ht : z 0∈Ioo a b := ⟨hza,hzb⟩
    have he0 := ((hreal 0 (z 0) (z 1) ht).mp hz0).deriv
    have he1 := ((hreal 1 (z 0) (z 2) ht).mp hz1).deriv
    have hh := h (z 0) ht
    fin_cases i <;> fin_cases k <;> simpa [he0,he1] using hh

def jointPlanarCoordinateGraphs {α : Type*} (P : Set (α → ℝ))
    (g : (α → ℝ) → ℝ → Fin 2 → ℝ) : Fin 2 → Set ((α ⊕ Fin 2) → ℝ) :=
  ![jointPlanarReadoutGraph P g 0,jointPlanarReadoutGraph P g 1]

theorem jointPlanarCoordinateGraphs_definable {α : Type} [Finite α]
    {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) (j : Fin 2) :
    (univ : Set ℝ).Definable Language.ring (jointPlanarCoordinateGraphs P g j) := by
  fin_cases j
  · exact jointPlanarReadoutGraph_definable hg 0
  · exact jointPlanarReadoutGraph_definable hg 1

theorem jointPlanarCoordinateGraphs_realize {α : Type*} (P : Set (α → ℝ))
    (g : (α → ℝ) → ℝ → Fin 2 → ℝ) {p : α → ℝ} (hp : p∈P)
    (j : Fin 2) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (y : ℝ) :
    Sum.elim p ![t,y] ∈ jointPlanarCoordinateGraphs P g j ↔ y=g p t j := by
  fin_cases j
  · simpa [jointPlanarCoordinateGraphs,planarReadout,planarReadoutPolynomial] using
      jointPlanarReadoutGraph_realize P g 0 hp ht y
  · simpa [jointPlanarCoordinateGraphs,planarReadout,planarReadoutPolynomial] using
      jointPlanarReadoutGraph_realize P g 1 hp ht y

theorem published_measurable_original_direction
    (hQE : PublishedRealSemialgebraicity)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (q : Ω → P) (hq : Measurable q)
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (haU : ∀ ω, a ω∈Icc (0:ℝ) 1) (hbU : ∀ ω, b ω∈Icc (0:ℝ) 1)
    (hd : ∀ ω j, DifferentiableOn ℝ (fun t => g (q ω).val t j) (Ioo (a ω) (b ω)))
    (he : ∀ ω, OriginalPlanarGraphArc (g (q ω).val) (a ω) (b ω)) :
    ∃ d : Ω → Fin 4, Measurable d ∧
      ∀ ω, PlanarDirectionCone (g (q ω).val) (a ω) (b ω) (d ω) ∧
        ∀ c<d ω, ¬ PlanarDirectionCone (g (q ω).val) (a ω) (b ω) c := by
  let G := jointPlanarCoordinateGraphs P g
  let Q (ω : Ω) (d : Fin 4) := Sum.elim (q ω).val ![a ω,b ω] ∈
    jointGraphConeTest G (planarDirectionI d) (planarDirectionK d) (planarDirectionSign d)
  have hreal (ω : Ω) (d : Fin 4) : Q ω d ↔ PlanarDirectionCone (g (q ω).val) (a ω) (b ω) d :=
    jointGraphConeTest_realize G (q ω).val (g (q ω).val)
      (jointPlanarCoordinateGraphs_realize P g (q ω).property)
      (haU ω) (hbU ω) (hd ω) _ _ _
  have hm : Measurable (fun ω => Sum.elim (q ω).val ![a ω,b ω]) := by
    apply measurable_pi_lambda
    intro r
    rcases r with r | r
    · exact (measurable_pi_apply r).comp (measurable_subtype_coe.comp hq)
    · fin_cases r
      · exact ha
      · exact hb
  have hQ (d : Fin 4) : MeasurableSet {ω | Q ω d} := by
    have hdef := jointGraphConeTest_definable G (jointPlanarCoordinateGraphs_definable hg)
      (planarDirectionI d) (planarDirectionK d) (planarDirectionSign d)
    have hset : MeasurableSet (jointGraphConeTest G (planarDirectionI d)
        (planarDirectionK d) (planarDirectionSign d)) := by
      convert hasPolynomialSignDescription_borel (hQE.finite_sign_description _ hdef)
      exact BorelSpace.measurable_eq
    exact hm hset
  refine ⟨fun ω => firstPlanarDirection (Q ω),measurable_firstPlanarDirection Q hQ,?_⟩
  intro ω
  have hex : ∃ d, Q ω d := by
    obtain ⟨d,hd⟩ := (he ω).exists_direction
    exact ⟨d,(hreal ω d).mpr hd⟩
  have hs := firstPlanarDirection_spec (Q ω) hex
  exact ⟨(hreal ω _).mp hs.1,fun c hc hcone => hs.2 c hc ((hreal ω c).mpr hcone)⟩

end PaperI
