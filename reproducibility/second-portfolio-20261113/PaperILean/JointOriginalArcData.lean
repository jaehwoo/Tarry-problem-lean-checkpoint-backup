import PaperILean.JointProjectedArcGraphs
import PaperILean.MeasurableFirstMaximum

/-! Original I1263/I1265: apply joint finite-direction and projected-graph
selection to the actual checkpoint152 cut partition, including endpoint
padding. The same data are retained; no path or cuts are reselected. -/
noncomputable section
namespace PaperI
open Set

theorem OriginalPlanarReadoutPartition.all_intervals
    {g : ℝ → Fin 2 → ℝ} {H n : ℕ} {t : ℕ → ℝ}
    (h : OriginalPlanarReadoutPartition g H n t) (hc : ContinuousOn g (Icc (0:ℝ) 1)) (j : ℕ) :
    t j∈Icc (0:ℝ) 1 ∧ t (j+1)∈Icc (0:ℝ) 1 ∧ t j≤t (j+1) ∧
      (∀ k, DifferentiableOn ℝ (fun r => g r k) (Ioo (t j) (t (j+1)))) ∧
      OriginalPlanarGraphArc g (t j) (t (j+1)) := by
  by_cases hj : j<n
  · obtain ⟨ha,hb,hab,hr⟩ := h.2.2.2.2.2.2 j hj
    refine ⟨ha,hb,hab.le,?_,h.graph_arcs hc j hj⟩
    intro k
    fin_cases k
    · simpa [planarReadout,planarReadoutPolynomial] using (hr 0).1.differentiableOn
    · simpa [planarReadout,planarReadoutPolynomial] using (hr 1).1.differentiableOn
  · have hjn : n≤j := Nat.le_of_not_gt hj
    have ha := h.2.2.2.2.2.1 j hjn
    have hb := h.2.2.2.2.2.1 (j+1) (by omega)
    rw [ha,hb]
    have hd : ∀ k, DifferentiableOn ℝ (fun r => g r k) (Ioo (1:ℝ) 1) := by
      intro k r hr
      exact (not_lt_of_ge hr.1.le hr.2).elim
    have hcone : ∀ r∈Ioo (1:ℝ) 1, |deriv (fun u => g u 1) r| ≤ 1*deriv (fun u => g u 0) r := by simp
    refine ⟨by simp,by simp,le_rfl,hd,0,1,1,?_,hcone⟩
    apply directedPlanarGraphArc_of_cone le_rfl _ hd 0 1 (by decide) 1 (Or.inl rfl) hcone
    intro k
    exact ((continuous_apply k).comp_continuousOn hc).mono (by intro x hx; simp_all)

def SelectedOriginalPlanarArc (g : ℝ → Fin 2 → ℝ) (a b : ℝ) (d : Fin 4)
    (F : ℝ → ℝ) : Prop :=
  DirectedPlanarGraphArc g a b (planarDirectionI d) (planarDirectionK d) (planarDirectionSign d) ∧
  PlanarDirectionCone g a b d ∧
  LipschitzOnWith 1 F
    (Icc (planarDirectionSign d*g a (planarDirectionI d))
      (planarDirectionSign d*g b (planarDirectionI d))) ∧
  (∀ r∈Icc a b, F (planarDirectionSign d*g r (planarDirectionI d))=g r (planarDirectionK d)) ∧
  ∀ q∈Icc (planarDirectionSign d*g a (planarDirectionI d))
      (planarDirectionSign d*g b (planarDirectionI d)),
    ∃ r∈Icc a b, q=planarDirectionSign d*g r (planarDirectionI d) ∧ F q=g r (planarDirectionK d)

theorem SelectedOriginalPlanarArc.tangent_projection
    {g : ℝ → Fin 2 → ℝ} {a b : ℝ} {d : Fin 4} {F : ℝ → ℝ}
    (h : SelectedOriginalPlanarArc g a b d F) {t : ℝ} (ht : t∈Ioo a b)
    (hspeed : 0 < (deriv (fun r => g r (planarDirectionI d)) t)^2 +
      (deriv (fun r => g r (planarDirectionK d)) t)^2) :
    (1/2:ℝ) ≤ planarDirectionSign d * deriv (fun r => g r (planarDirectionI d)) t /
      Real.sqrt ((deriv (fun r => g r (planarDirectionI d)) t)^2 +
        (deriv (fun r => g r (planarDirectionK d)) t)^2) := by
  apply dominant_nonzero_normalized_projection_half
    (v := deriv (fun r => g r (planarDirectionK d)) t) (Real.sqrt_pos.mpr hspeed)
  · rw [Real.sq_sqrt hspeed.le]
    rcases planarDirection_sign d with hs | hs <;> simp [hs]
  · exact h.2.1 t ht

theorem published_joint_original_partition_arc_data
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity)
    (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (q : Ω → P) (hq : Measurable q)
    (H : ℕ) (n : Ω → ℕ) (t : Ω → ℕ → ℝ)
    (ht : ∀ j, Measurable (fun ω => t ω j))
    (hpart : ∀ ω, OriginalPlanarReadoutPartition (g (q ω).val) H (n ω) (t ω))
    (hc : ∀ ω, ContinuousOn (g (q ω).val) (Icc (0:ℝ) 1)) :
    ∃ (d : Ω × ℕ → Fin 4) (F : (Ω × ℕ) × ℝ → ℝ), Measurable d ∧ Measurable F ∧
      ∀ ω j, SelectedOriginalPlanarArc (g (q ω).val) (t ω j) (t ω (j+1))
        (d (ω,j)) (fun x => F ((ω,j),x)) ∧
        ∀ c<d (ω,j), ¬ PlanarDirectionCone (g (q ω).val) (t ω j) (t ω (j+1)) c := by
  classical
  let a : Ω × ℕ → ℝ := fun v => t v.1 v.2
  let b : Ω × ℕ → ℝ := fun v => t v.1 (v.2+1)
  have ha : Measurable a := measurable_from_prod_countable ht
  have hb : Measurable b := measurable_from_prod_countable (fun j => ht (j+1))
  have hall (v : Ω × ℕ) := (hpart v.1).all_intervals (hc v.1) v.2
  obtain ⟨d,hdm,hd⟩ := published_measurable_original_direction hQE hg (q ∘ Prod.fst)
    (hq.comp measurable_fst) a b ha hb (fun v => (hall v).1) (fun v => (hall v).2.1)
    (fun v => (hall v).2.2.2.1) (fun v => (hall v).2.2.2.2)
  have hdir (v : Ω × ℕ) : DirectedPlanarGraphArc (g (q v.1).val) (a v) (b v)
      (planarDirectionI (d v)) (planarDirectionK (d v)) (planarDirectionSign (d v)) := by
    apply directedPlanarGraphArc_of_cone (hall v).2.2.1 _ (hall v).2.2.2.1
      _ _ (planarDirection_distinct _) _ (planarDirection_sign _) (hd v).1
    intro k
    exact ((continuous_apply k).comp_continuousOn (hc v.1)).mono
      (Icc_subset_Icc (hall v).1.1 (hall v).2.1.2)
  choose Fs hFm hFs hF using fun c : Fin 4 => published_joint_projected_arc_graph hCAD hQE hHardt hg
    (planarDirectionI c) (planarDirectionK c) (planarDirectionSign c)
  let enc : (Ω × ℕ) × ℝ → (α ⊕ Fin 3) → ℝ :=
    fun v => Sum.elim (q v.1.1).val ![a v.1,b v.1,v.2]
  have henc : Measurable enc := by
    apply measurable_pi_lambda
    intro r
    rcases r with r | r
    · exact (measurable_pi_apply r).comp
        (measurable_subtype_coe.comp (hq.comp (measurable_fst.comp measurable_fst)))
    · fin_cases r
      · exact ha.comp measurable_fst
      · exact hb.comp measurable_fst
      · exact measurable_snd
  have hswitch : Measurable (fun v : ((α ⊕ Fin 3) → ℝ) × Fin 4 => Fs v.2 v.1) :=
    measurable_from_prod_countable hFm
  let F : (Ω × ℕ) × ℝ → ℝ := fun v => Fs (d v.1) (enc v)
  refine ⟨d,F,hdm,hswitch.comp (henc.prodMk (hdm.comp measurable_fst)),?_⟩
  intro ω j
  have hproj := hF (d (ω,j)) (q ω).val (q ω).property (a (ω,j)) (hall (ω,j)).1
    (b (ω,j)) (hall (ω,j)).2.1 (hall (ω,j)).2.2.1 (hdir (ω,j))
  exact ⟨⟨hdir (ω,j),(hd (ω,j)).1,hproj⟩,(hd (ω,j)).2⟩

end PaperI
