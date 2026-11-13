import PaperILean.OriginalJointArcCertificates

/-! I1263/I1265: apply the original preparation engine to ANY actual selected
graph of the retained joint path. Graph uniqueness identifies it with the
fixed four selectors on the whole closed interval. No graph is reselected. -/
noncomputable section
namespace PaperI
open Set

def OriginalPreparedGraphInterval (f : ℝ → ℝ) (a b u v C : ℝ) (K N : ℕ) : Prop :=
  u<v ∧ Icc u v⊆Icc a b ∧ (b-a)/(K : ℝ)≤v-u ∧
    AnalyticOnNhd ℝ f (Icc u v) ∧
    (∀ x∈Icc u v, ∀ n≤N,
      |iteratedDeriv n (fun q => f q-f a) x|≤C*(b-a)/(b-a)^n) ∧
    (∀ x∈Icc u v, ∀ n, 0<n → n≤N →
      |iteratedDeriv n f x|≤C*(b-a)/(b-a)^n)

theorem OriginalJointArcSelectorFamily.preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (S : OriginalJointArcSelectorFamily P g) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (p : Ω → α → ℝ) (a b : Ω → ℝ)
      (d : Ω → Fin 4) (f : Ω → ℝ → ℝ) (A B : Ω → ℝ),
      Measurable p → Measurable a → Measurable b → Measurable d →
      Measurable A → Measurable B → (∀ ω, A ω<B ω) →
      (∀ ω x, x∈Icc (A ω) (B ω) →
        f ω x=S.selector (d ω) (Sum.elim (p ω) ![a ω,b ω,x])) →
      (∀ ω, LipschitzOnWith 1 (f ω) (Icc (A ω) (B ω))) →
      ∃ u v : Ω → ℝ, Measurable u ∧ Measurable v ∧
        ∀ ω, OriginalPreparedGraphInterval (f ω) (A ω) (B ω) (u ω) (v ω) C K N := by
  obtain ⟨C,hC,K,hK,hprep⟩ := published_joint_original_lipschitz_prepared_interval
    hDD hCAD hCell hHardt hQE hPiece (jointOriginalArcScalarGraph S.selector)
    (jointOriginalArcScalarGraph_definable S.selector S.semialgebraic_graph) N
  refine ⟨C,hC,K,hK,?_⟩
  intro Ω inst p a b d f A B hp ha hb hd hA hB hab hsame hLip
  let q : Ω → (α ⊕ Fin 3) → ℝ :=
    fun ω => Sum.elim (p ω) ![a ω,b ω,((d ω).val : ℝ)]
  have hcode : Measurable (fun ω => ((d ω).val : ℝ)) :=
    (measurable_of_countable (fun c : Fin 4 => (c.val : ℝ))).comp hd
  have hq : Measurable q := by
    apply measurable_pi_lambda
    intro j
    rcases j with j | j
    · exact (measurable_pi_apply j).comp hp
    · fin_cases j <;> assumption
  apply hprep Ω q f A B hq hA hB hab
  · intro ω x hx y
    rw [jointOriginalArcScalarGraph_realize]
    rw [hsame ω x hx]
  · exact hLip

theorem published_joint_path_signed_coordinate_measurable
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (p : Ω → P) (t : Ω → ℝ) (d : Ω → Fin 4)
    (hp : Measurable p) (ht : Measurable t) (hd : Measurable d)
    (htU : ∀ ω, t ω∈Icc (0:ℝ) 1) :
    Measurable (fun ω => planarDirectionSign (d ω)*g (p ω).val (t ω) (planarDirectionI (d ω))) := by
  have htime : Measurable (fun ω => (⟨t ω,htU ω⟩ : Icc (0:ℝ) 1)) := ht.subtype_mk
  have heval : Measurable (fun ω => g (p ω).val (t ω)) :=
    (published_jointUnitPath_measurable hQE hHardt hg).comp (hp.prodMk htime)
  have hm : Measurable (fun v : Ω × Fin 4 =>
      planarDirectionSign v.2*g (p v.1).val (t v.1) (planarDirectionI v.2)) := by
    apply measurable_from_prod_countable
    intro c
    exact ((measurable_pi_apply _).comp heval).const_mul _
  exact hm.comp (measurable_id.prodMk hd)

theorem OriginalJointArcSelectorFamily.prepare_selected_arcs
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    (S : OriginalJointArcSelectorFamily P g) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (p : Ω → P) (a b : Ω → ℝ)
      (d : Ω → Fin 4) (f : Ω → ℝ → ℝ),
      Measurable p → Measurable a → Measurable b → Measurable d →
      (∀ ω, a ω∈Icc (0:ℝ) 1) → (∀ ω, b ω∈Icc (0:ℝ) 1) → (∀ ω, a ω≤b ω) →
      (∀ ω, SelectedOriginalPlanarArc (g (p ω).val) (a ω) (b ω) (d ω) (f ω)) →
      (∀ ω, planarDirectionSign (d ω)*g (p ω).val (a ω) (planarDirectionI (d ω)) <
        planarDirectionSign (d ω)*g (p ω).val (b ω) (planarDirectionI (d ω))) →
      ∃ u v : Ω → ℝ, Measurable u ∧ Measurable v ∧ ∀ ω,
        OriginalPreparedGraphInterval (f ω)
          (planarDirectionSign (d ω)*g (p ω).val (a ω) (planarDirectionI (d ω)))
          (planarDirectionSign (d ω)*g (p ω).val (b ω) (planarDirectionI (d ω)))
          (u ω) (v ω) C K N := by
  obtain ⟨C,hC,K,hK,hprep⟩ := S.preparation hDD hCAD hCell hHardt hQE hPiece N
  refine ⟨C,hC,K,hK,?_⟩
  intro Ω inst p a b d f hp ha hb hd haU hbU hab hArc hspan
  apply hprep Ω (fun ω => (p ω).val) a b d f _ _
    (measurable_subtype_coe.comp hp) ha hb hd
    (published_joint_path_signed_coordinate_measurable hQE hHardt hg p a d hp ha hd haU)
    (published_joint_path_signed_coordinate_measurable hQE hHardt hg p b d hp hb hd hbU) hspan
  · intro ω x hx
    have hproj := S.correct (d ω) (p ω).val (p ω).property (a ω) (haU ω)
      (b ω) (hbU ω) (hab ω) (hArc ω).1
    exact (hArc ω).eqOn ⟨(hArc ω).1,(hArc ω).2.1,hproj⟩ hx
  · exact fun ω => (hArc ω).2.2.1

end PaperI
