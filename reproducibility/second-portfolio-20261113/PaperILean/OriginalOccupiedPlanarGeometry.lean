import PaperILean.OriginalMeasurablePlanarAssignment

/-! I1245-I1265: all quantitative bounds at an occupied original piece.
Every assigned label uses the SAME strip; endpoint estimates are at each
assigned planar point. This does not assert the separate Gauss chart bridge.
-/
noncomputable section
namespace PaperI
open Set Metric MeasureTheory

theorem originalDyadicAssigned_common_rounded_geometry
    {Ω Λ : Type*} {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (B : Fin D.count → OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω) (j : Λ) (k : ℤ) (i : Fin D.count)
    (H K N m : ℕ) (C P mass : ℝ)
    (hpack : OriginalDyadicPackingBounds D active param radius point ω m P mass)
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i)
    (hcomponent : (B i).ComponentStripAt D i H K N C
      (originalDyadicPositiveParameters param radius k ω))
    (hrounded : (B i).RoundedComponentAt D i N (P^m)
      (originalDyadicPositiveParameters param radius k ω))
    {E : Set (EuclideanSpace ℝ (Fin 2))} (ho : IsOpen E) (hb : Bornology.IsBounded E)
    (hT : 0≤radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω)) :
    let p := originalDyadicPositiveParameters param radius k ω
    let W0 := (2:ℝ)^k
    let L := roundedDyadicScale (originalJointComponentScale D i p.val)
    let W := roundedDyadicScale W0
    let I := {j' | originalDyadicComponentAssigned D active param radius point ω j' k i}
    let Cset := (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber (D.part i) p.val
    let S := originalAssignedPlanarStrip D B active param radius point ω j
    I.Finite ∧ (I.ncard : ℝ)≤P^m*mass*L*W ∧
      Metric.diam ((fun j' => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j')) '' I)≤L ∧
      1≤W ∧ W≤L ∧ (B i).PhysicalPreparedAt N (P^m) L p ∧
      L/(P^m)≤(B i).right p-(B i).left p ∧ (B i).right p-(B i).left p≤L ∧
      W/(P^m)≤W0/4 ∧ W0/4≤W ∧
      S⊆E ∧ MeasurableSet S ∧ volume.real S=((B i).right p-(B i).left p)*W0/2 ∧
      L*W/(P^m)≤volume.real S ∧
      ∀ j'∈I,
        let a := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j')
        originalAssignedPlanarStrip D B active param radius point ω j'=S ∧
        Cset∪S⊆closedBall a (2*L) ∧
        volume (relativePlanarEndpoints a (Cset∪S))≤ENNReal.ofReal (P^m*L^2) ∧
        volume (relativePlanarEndpoints a (Cset∪S))≠⊤ ∧
        volume.real (relativePlanarEndpoints a (Cset∪S))≤P^m*L^2 := by
  let p := originalDyadicPositiveParameters param radius k ω
  let W0 := (2:ℝ)^k
  let L := roundedDyadicScale (originalJointComponentScale D i p.val)
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ((B i).anchor p)
  let Cset := (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' projectionFiber (D.part i) p.val
  let S := (B i).strip p W0
  have hW0 : 0<W0 := zpow_pos (by norm_num) k
  have hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z∈projectionFiber (D.part i) p.val := by
    simpa only [z,Equiv.apply_symm_apply] using hcomponent.1
  have hCsub : Cset⊆bufferedBandComponent E W0 z := by
    rintro x ⟨y,hy,rfl⟩
    exact originalJointEndpoint_mem_actual_component D (param ω) hT hW0 ho hE hbox i z hz hy
  have hstrip := originalAssignedPlanarStrip_eq D B active param radius point ω j (hpack.1 j) (k,i) hj
  rcases hrounded with ⟨hQ,hW,hWL,hprep,hlenlo,hlenhi,hwlo,hwhi,hgeom⟩
  rcases hgeom E hT ho hb hE hbox with ⟨hSE,hSm,harea,hareaLow,hcontrols⟩
  have hcount := hpack.2.2.2 k i
  dsimp only
  rw [hstrip]
  refine ⟨hcount.1,hcount.2.1,hcount.2.2.2,hW,hWL,hprep,hlenlo,hlenhi,hwlo,hwhi,
    hSE,hSm,harea,hareaLow,?_⟩
  intro j' hj'
  have hpoint := originalJointEndpoint_mem_actual_component D (param ω) hT hW0 ho hE hbox i z hz hj'.2
  rcases hcontrols _ hpoint with ⟨hball,houter,_,_⟩
  let a := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j')
  have hreg : Cset∪S⊆bufferedBandComponent E W0 z∪S := union_subset_union hCsub Subset.rfl
  have hrel : relativePlanarEndpoints a (Cset∪S)⊆
      relativePlanarEndpoints a (bufferedBandComponent E W0 z∪S) := image_mono hreg
  have houter' : volume (relativePlanarEndpoints a (Cset∪S))≤ENNReal.ofReal (P^m*L^2) :=
    (measure_mono hrel).trans houter
  exact ⟨originalAssignedPlanarStrip_eq D B active param radius point ω j' (hpack.1 j') (k,i) hj',
    hreg.trans hball,houter',
    planar_finite_real_area_of_outer_bound (mul_nonneg (zero_le_one.trans hQ) (sq_nonneg L)) houter'⟩

end PaperI
