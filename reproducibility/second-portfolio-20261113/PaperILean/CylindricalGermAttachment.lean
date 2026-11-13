import PaperILean.CylindricalTowerSection
import PaperILean.JointCurveSelection

/-! A germ constructed from a cylindrical cell over an initial time band.
The section is constructed by the explicit recursive formulas, not supplied
as a curve. Existence of the appropriate band and cell for an ambient input
is deliberately not assumed as a published theorem in this file. -/

noncomputable section
namespace PaperI
open Set FirstOrder Filter
open scoped Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def cadInitialBand {ρ : Type} (P : Set (ρ → ℝ)) (β : (ρ → ℝ) → ℝ) :
    Set ((ρ ⊕ Unit) → ℝ) :=
  {v | v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr ()) ∧ v (Sum.inr ()) < β (v ∘ Sum.inl)}

theorem cadInitialBand_definable {ρ : Type} [Finite ρ]
    {P : Set (ρ → ℝ)} {β : (ρ → ℝ) → ℝ}
    (hβ : (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph P (fun p (_ : Unit) => β p))) :
    (univ : Set ℝ).Definable Language.ring (cadInitialBand P β) := by
  let e : ρ ⊕ Unit → (ρ ⊕ Unit) ⊕ Unit := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have hpos := realPolynomial_lt_definable (0 : MvPolynomial ((ρ ⊕ Unit) ⊕ Unit) ℝ)
    (MvPolynomial.X (Sum.inl (Sum.inr ())))
  have hlt := realCoordinate_lt_definable (Sum.inl (Sum.inr ()) : (ρ ⊕ Unit) ⊕ Unit) (Sum.inr ())
  have h := realDefinable_exists ((hβ.preimage_comp e).inter (hpos.inter hlt))
  convert h using 1
  ext v
  change (v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr ()) ∧ v (Sum.inr ()) < β (v ∘ Sum.inl)) ↔ _
  have he (r : Unit → ℝ) : Sum.elim v r ∘ e = Sum.elim (v ∘ Sum.inl) r := by
    funext i; cases i <;> rfl
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, he, selectedFunctionGraph,
    MvPolynomial.eval_X, map_zero, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hp,ht,hb⟩
    exact ⟨fun _ => β (v ∘ Sum.inl),⟨hp,rfl⟩,ht,hb⟩
  · rintro ⟨r,⟨hp,hr⟩,ht,hb⟩
    exact ⟨hp,ht,by simpa only [← hr] using hb⟩

theorem cad_attachAtZero_continuousOn {ρ κ : Type} [Fintype κ]
    (a : (ρ → ℝ) → κ → ℝ) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (p : ρ → ℝ) (ε : ℝ)
    (hnear : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ k, |f (Sum.elim p (fun _ => t)) k - a p k| < t)
    (hc : ContinuousOn (fun t => f (Sum.elim p (fun _ => t))) (Ioo (0 : ℝ) ε)) :
    ContinuousOn (attachAtZero a f p) (Ico (0 : ℝ) ε) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    apply Metric.continuousWithinAt_iff.mpr
    intro η hη
    refine ⟨η,hη,fun u hu huη => ?_⟩
    by_cases hu0 : u = 0
    · simpa only [hu0, dist_self] using hη
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [attachAtZero_zero, attachAtZero_positive a f p huPos]
    apply (dist_pi_lt_iff hη).mpr
    intro k
    rw [Real.dist_eq]
    exact (hnear u ⟨huPos,hu.2⟩ k).trans
      (by simpa only [Real.dist_eq,sub_zero,abs_of_pos huPos] using huη)
  · have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hfAt := (hc t ⟨htPos,ht.2⟩).continuousAt (isOpen_Ioo.mem_nhds ⟨htPos,ht.2⟩)
    apply ContinuousAt.continuousWithinAt
    apply hfAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds htPos] with u hu
    exact attachAtZero_positive a f p hu

theorem cad_jointGermGraph_attach_definable {ρ κ : Type} [Finite ρ] [Finite κ]
    (P : Set (ρ → ℝ)) (β : (ρ → ℝ) → ℝ)
    (a : (ρ → ℝ) → κ → ℝ) (f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ)
    (ha : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a))
    (hf : (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph (cadInitialBand P β) f))
    (hpos : ∀ p ∈ P, 0 < β p) :
    (univ : Set ℝ).Definable Language.ring
      (jointCurveGermGraph P β (attachAtZero a f)) := by
  let B := ρ ⊕ (Unit ⊕ κ)
  let eA : ρ ⊕ κ → B := Sum.elim Sum.inl (fun k => Sum.inr (Sum.inr k))
  let eF : (ρ ⊕ Unit) ⊕ κ → B :=
    Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Sum.inl ()))) (fun k => Sum.inr (Sum.inr k))
  have hz := (realPolynomial_zero_definable (MvPolynomial.X (Sum.inr (Sum.inl ()) : B))).inter
    (ha.preimage_comp eA)
  convert hz.union (hf.preimage_comp eF) using 1
  ext v
  have heA : v ∘ eA = Sum.elim (v ∘ Sum.inl) (fun k => v (Sum.inr (Sum.inr k))) := by
    funext i; cases i <;> rfl
  have heF : v ∘ eF = Sum.elim (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr (Sum.inl ()))))
      (fun k => v (Sum.inr (Sum.inr k))) := by
    funext i; rcases i with (i | ⟨⟩) | k <;> rfl
  simp only [mem_union,mem_inter_iff,mem_setOf_eq,mem_preimage,heA,heF,
    MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr]
  change (_ ∧ _ ∧ _) ↔
    (v (Sum.inr (Sum.inl ())) = 0 ∧ (v ∘ Sum.inl ∈ P ∧
      a (v ∘ Sum.inl) = fun k => v (Sum.inr (Sum.inr k)))) ∨
    ((v ∘ Sum.inl ∈ P ∧ 0 < v (Sum.inr (Sum.inl ())) ∧
      v (Sum.inr (Sum.inl ())) < β (v ∘ Sum.inl)) ∧
      f (Sum.elim (v ∘ Sum.inl) (fun _ => v (Sum.inr (Sum.inl ())))) =
        fun k => v (Sum.inr (Sum.inr k)))
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨hp,ht,hy⟩
    by_cases ht0 : v (Sum.inr (Sum.inl ())) = 0
    · exact Or.inl ⟨ht0,hp,by simpa only [attachAtZero,ht0,if_pos rfl] using hy.symm⟩
    · exact Or.inr ⟨⟨hp,lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩,
        by simpa only [attachAtZero,ht0,if_false] using hy.symm⟩
  · rintro (⟨ht0,hp,hy⟩ | ⟨⟨hp,ht,hb⟩,hy⟩)
    · refine ⟨hp,⟨by rw [ht0],by simpa only [ht0] using hpos _ hp⟩,?_⟩
      simpa only [attachAtZero,ht0,if_pos rfl] using hy.symm
    · exact ⟨hp,⟨ht.le,hb⟩,by simpa only [attachAtZero,ne_of_gt ht,if_false] using hy.symm⟩

theorem cylindricalTower_joint_germ {ρ κ : Type} [Finite ρ] [Fintype κ]
    (P : Set (ρ → ℝ)) (β : (ρ → ℝ) → ℝ)
    (C : Set ((ρ ⊕ κ) → ℝ)) (a : (ρ → ℝ) → κ → ℝ)
    (hβ : (univ : Set ℝ).Definable Language.ring
      (selectedFunctionGraph P (fun p (_ : Unit) => β p)))
    (ha : (univ : Set ℝ).Definable Language.ring (selectedFunctionGraph P a))
    (hpos : ∀ p ∈ P, 0 < β p)
    {n : ℕ} {S : Set (CADVariables (ρ ⊕ Unit) n → ℝ)}
    (c : CylindricalTower (cadInitialBand P β) S)
    (output : κ → CADVariables (ρ ⊕ Unit) n)
    (hcell : ∀ z ∈ S,
      z ∘ output ∈ projectionFiber C (z ∘ cadBaseCoordinate n ∘ Sum.inl) ∧
      ∀ k, |z (output k) - a (z ∘ cadBaseCoordinate n ∘ Sum.inl) k| <
        z (cadBaseCoordinate n (Sum.inr ()))) :
    ∃ g : (ρ → ℝ) → ℝ → κ → ℝ,
      (univ : Set ℝ).Definable Language.ring (jointCurveGermGraph P β g) ∧
      ∀ p ∈ P, g p 0 = a p ∧ ContinuousOn (g p) (Ico (0 : ℝ) (β p)) ∧
        MapsTo (g p) (Ioo (0 : ℝ) (β p)) (projectionFiber C p) := by
  let f : ((ρ ⊕ Unit) → ℝ) → κ → ℝ := fun v => c.sectionMap v ∘ output
  have hband := cadInitialBand_definable hβ
  have hf := cad_selectedGraph_comp (c.sectionMap_graph_definable hband)
    (coordinateSectionGraph_definable (c.region_definable hband) output)
    (fun _ hv => c.sectionMap_mem hv)
  have hval (p : ρ → ℝ) (hp : p ∈ P) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (β p)) :
      f (Sum.elim p (fun _ => t)) ∈ projectionFiber C p ∧
      ∀ k, |f (Sum.elim p (fun _ => t)) k - a p k| < t := by
    have h := hcell _ (c.sectionMap_mem (show Sum.elim p (fun _ => t) ∈ cadInitialBand P β from ⟨hp,ht⟩))
    have hb := c.sectionMap_projection (Sum.elim p (fun _ => t))
    have hp' : c.sectionMap (Sum.elim p (fun _ : Unit => t)) ∘ cadBaseCoordinate n ∘ Sum.inl = p := by
      funext r
      exact congrFun hb (Sum.inl r)
    have ht' : c.sectionMap (Sum.elim p (fun _ : Unit => t)) (cadBaseCoordinate n (Sum.inr ())) = t :=
      congrFun hb (Sum.inr ())
    rw [hp',ht'] at h
    exact h
  refine ⟨attachAtZero a f,cad_jointGermGraph_attach_definable P β a f ha hf hpos,?_⟩
  intro p hp
  have hfc : ContinuousOn (fun t => f (Sum.elim p (fun _ => t))) (Ioo (0 : ℝ) (β p)) := by
    have htime : Continuous (fun t : ℝ => Sum.elim p (fun _ : Unit => t)) := by
      apply continuous_pi
      intro i
      cases i with
      | inl r => exact continuous_const
      | inr u => exact continuous_id
    have htower := c.sectionMap_continuousOn.comp htime.continuousOn
      (fun _ ht => (show Sum.elim p (fun _ : Unit => _) ∈ cadInitialBand P β from ⟨hp,ht⟩))
    exact continuousOn_pi.mpr (fun k => (continuous_apply (output k)).continuousOn.comp htower
      (fun _ _ => mem_univ _))
  refine ⟨attachAtZero_zero a f p,
    cad_attachAtZero_continuousOn a f p (β p) (fun t ht => (hval p hp t ht).2) hfc,?_⟩
  intro t ht
  rw [attachAtZero_positive a f p ht.1]
  exact (hval p hp t ht).1

end PaperI
