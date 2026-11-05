import PaperILean.PublishedHardtTriviality
import PaperILean.SemialgebraicPathData

/-! Checked transport through a semialgebraic Hardt chart. The extra data keep
the chart's actual graph and compatibility with two marked subsets; this module
does not provide that data or assume a uniform path conclusion. -/

noncomputable section
namespace PaperI
open Set

def ProjectionHardtData.chartGraph {ρ κ : Type*} {A : Set ((ρ ⊕ κ) → ℝ)}
    (D : ProjectionHardtData A) (i : Fin D.n) : Set (((ρ ⊕ κ) ⊕ κ) → ℝ) :=
  {v | ∃ (hp : (fun r => v (Sum.inl (Sum.inl r))) ∈ D.piece i)
      (hx : (fun k => v (Sum.inl (Sum.inr k))) ∈
        projectionFiber A (D.basePoint i).val),
    (fun k => v (Sum.inr k)) =
      (D.chart i (⟨_, hp⟩, ⟨_, hx⟩)).val.2}

structure CompatibleProjectionHardtData {ρ κ : Type*}
    (A : Set ((ρ ⊕ κ) → ℝ)) (mark : Fin 2 → Set ((ρ ⊕ κ) → ℝ))
    extends ProjectionHardtData A where
  chart_semialgebraic : ∀ i, HasPolynomialSignDescription (toProjectionHardtData.chartGraph i)
  compatible : ∀ i (p : piece i) (x : projectionFiber A (basePoint i).val) (j : Fin 2),
    Sum.elim p.val (chart i (p, x)).val.2 ∈ mark j ↔
      Sum.elim (basePoint i).val (chart i (basePoint i, x)).val.2 ∈ mark j

def endpointGraph {ρ κ : Type*} (A : Set ((ρ ⊕ κ) → ℝ))
    (e : (ρ → ℝ) → κ → ℝ) : Set ((ρ ⊕ κ) → ℝ) :=
  {v | (fun r => v (Sum.inl r)) ∈ projectionDomain A ∧
    (fun k => v (Sum.inr k)) = e (fun r => v (Sum.inl r))}

def CompatibleProjectionHardtData.referenceEndpoint {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (D : CompatibleProjectionHardtData A (fun j => endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p)
    (i : Fin D.n) (j : Fin 2) : projectionFiber A (D.basePoint i).val :=
  (D.toProjectionHardtData.fiberHomeomorph i (D.basePoint i)).symm
    ⟨e j (D.basePoint i).val, he j _ (D.piece_subset i (D.basePoint i).property)⟩

theorem CompatibleProjectionHardtData.chart_endpoint {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (D : CompatibleProjectionHardtData A (fun j => endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p)
    (i : Fin D.n) (p : D.piece i) (j : Fin 2) :
    (D.chart i (p, D.referenceEndpoint e he i j)).val.2 = e j p.val := by
  apply ((D.compatible i p _ j).mpr ?_).2
  refine ⟨D.piece_subset i (D.basePoint i).property, ?_⟩
  change ((D.toProjectionHardtData.fiberHomeomorph i (D.basePoint i))
    ((D.toProjectionHardtData.fiberHomeomorph i (D.basePoint i)).symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

def ProjectionHardtData.transportPath {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b)
    (t : ℝ) : κ → ℝ :=
  if ht : t ∈ Icc (0 : ℝ) 1 then
    (D.chart i (p, ⟨γ.toFun t, γ.mapsTo ht⟩)).val.2 else 0

theorem ProjectionHardtData.transportPath_eq {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    D.transportPath i p γ t =
      (D.chart i (p, ⟨γ.toFun t, γ.mapsTo ht⟩)).val.2 := by
  simp only [transportPath, dif_pos ht]

theorem ProjectionHardtData.transportPath_mapsTo {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b) :
    MapsTo (D.transportPath i p γ) (Icc (0 : ℝ) 1) (projectionFiber A p.val) := by
  intro t ht
  rw [D.transportPath_eq i p γ ht]
  have h := (D.chart i (p, ⟨γ.toFun t, γ.mapsTo ht⟩)).property.2
  rw [D.projection_chart] at h
  exact h

theorem ProjectionHardtData.transportPath_continuousOn {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (D : ProjectionHardtData A)
    (i : Fin D.n) (p : D.piece i) {a b : κ → ℝ}
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val) a b) :
    ContinuousOn (D.transportPath i p γ) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun t : Icc (0 : ℝ) 1 =>
      (D.chart i (p, ⟨γ.toFun t.val, γ.mapsTo t.property⟩)).val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp
      ((D.chart i).continuous.comp (continuous_const.prodMk
        (γ.continuousOn.restrict.subtype_mk _))))
  convert h using 1
  funext t
  exact D.transportPath_eq i p γ t.property

theorem CompatibleProjectionHardtData.transportPath_endpoints {ρ κ : Type*}
    {A : Set ((ρ ⊕ κ) → ℝ)} (e : Fin 2 → (ρ → ℝ) → κ → ℝ)
    (D : CompatibleProjectionHardtData A (fun j => endpointGraph A (e j)))
    (he : ∀ j p, p ∈ projectionDomain A → e j p ∈ projectionFiber A p)
    (i : Fin D.n) (p : D.piece i)
    (γ : SemialgebraicUnitPath (projectionFiber A (D.basePoint i).val)
      (D.referenceEndpoint e he i 0).val (D.referenceEndpoint e he i 1).val) :
    D.toProjectionHardtData.transportPath i p γ 0 = e 0 p.val ∧
    D.toProjectionHardtData.transportPath i p γ 1 = e 1 p.val := by
  constructor
  · rw [D.toProjectionHardtData.transportPath_eq i p γ (by simp)]
    have hx : (⟨γ.toFun 0, γ.mapsTo (by simp)⟩ :
        projectionFiber A (D.basePoint i).val) = D.referenceEndpoint e he i 0 :=
      Subtype.ext γ.source
    simpa only [hx] using D.chart_endpoint e he i p 0
  · rw [D.toProjectionHardtData.transportPath_eq i p γ (by simp)]
    have hx : (⟨γ.toFun 1, γ.mapsTo (by simp)⟩ :
        projectionFiber A (D.basePoint i).val) = D.referenceEndpoint e he i 1 :=
      Subtype.ext γ.target
    simpa only [hx] using D.chart_endpoint e he i p 1

end PaperI
