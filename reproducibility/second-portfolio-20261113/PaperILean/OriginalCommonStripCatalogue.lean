import PaperILean.OriginalCommonComponentStrip

/-! Constants precede Boolean tables, coefficients, T, W, components and
all Borel pullbacks. Original labels use the SAME component strip. This is
not yet the packing/rounding/count assembly of the entire planar lemma. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

theorem published_inputFormat_original_common_strips
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (s d N : ℕ) :
    ∃ Nc H K : ℕ, 2≤H ∧ 0<K ∧ ∃ C : ℝ, 1≤C ∧
      ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition
        (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count≤Nc ∧ ∀ i : Fin D.count,
          ∃ B : OriginalBorelStripFamily
            (originalJointPositiveWidthDomain (Fin s × (Fin 2 → Fin (d+1)))),
            ∀ p, (projectionFiber (D.part i) p.val).Nonempty →
              B.ComponentStripAt D i H K N C p := by
  obtain ⟨Nc,sp,dp,H,hH,C,hC,K,hK,hall⟩ :=
    published_inputFormat_original_prepared_components hDD hCAD hCell hHardt hQE hPiece s d N
  refine ⟨Nc,H,K,hH,hK,C*(4*(H : ℝ))^N,
    prepared_arc_scale_constant_ge_one hC (by exact_mod_cast (show 1≤4*H by omega)) N,?_⟩
  intro b
  obtain ⟨D,hcount,hF⟩ := hall b
  refine ⟨D,hcount,?_⟩
  intro i
  obtain ⟨F⟩ := (hF i).1
  exact F.common_component_strip hCAD hQE hHardt.toHardtTriviality D i hH hC hK

def originalDyadicPositiveParameters {Ω ρ : Type*}
    (param : Ω → ρ → ℝ) (radius : Ω → ℝ) (k : ℤ) :
    Ω → originalJointPositiveWidthDomain ρ :=
  fun ω => ⟨Sum.elim (Sum.elim (param ω) (fun _ => radius ω)) (fun _ => (2:ℝ)^k),
    zpow_pos (by norm_num : (0 : ℝ)<2) k⟩

theorem measurable_originalDyadicPositiveParameters {Ω ρ : Type*}
    [MeasurableSpace Ω] (param : Ω → ρ → ℝ) (radius : Ω → ℝ) (k : ℤ)
    (hp : Measurable param) (hT : Measurable radius) :
    Measurable (originalDyadicPositiveParameters param radius k) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro r
  rcases r with (r | u) | u
  · exact (measurable_pi_apply r).comp hp
  · exact hT
  · exact measurable_const

theorem originalDyadicComponentAssigned_common_strip
    {Ω Λ : Type*} {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (H K N : ℕ) (C : ℝ)
    (hB : ∀ p, (projectionFiber (D.part i) p.val).Nonempty → B.ComponentStripAt D i H K N C p)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ}
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    B.ComponentStripAt D i H K N C (originalDyadicPositiveParameters param radius k ω) :=
  hB _ ⟨point ω j,hj.2⟩

theorem originalDyadicCommonStrip_measurable
    {Ω ρ : Type*} [MeasurableSpace Ω]
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (param : Ω → ρ → ℝ) (radius : Ω → ℝ) (k : ℤ)
    (hp : Measurable param) (hT : Measurable radius) :
    MeasurableSet {v : Ω × WithLp 2 (Fin 2 → ℝ) |
      v.2∈B.strip (originalDyadicPositiveParameters param radius k v.1) ((2:ℝ)^k)} :=
  (B.comp (originalDyadicPositiveParameters param radius k)
    (measurable_originalDyadicPositiveParameters param radius k hp hT)).measurableSet_joint_strip
    (fun _ => (2:ℝ)^k) measurable_const

theorem originalDyadicCommonStrip_same_parameters
    {Ω ρ : Type*} (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (param : Ω → ρ → ℝ) (radius : Ω → ℝ) {ω ξ : Ω} (k : ℤ)
    (hp : param ω=param ξ) (hT : radius ω=radius ξ) :
    B.strip (originalDyadicPositiveParameters param radius k ω) ((2:ℝ)^k)=
      B.strip (originalDyadicPositiveParameters param radius k ξ) ((2:ℝ)^k) := by
  have hq : originalDyadicPositiveParameters param radius k ω=
      originalDyadicPositiveParameters param radius k ξ := by
    apply Subtype.ext
    simp only [originalDyadicPositiveParameters,hp,hT]
  rw [hq]

theorem originalDyadicCommonStrip_assigned_endpoint_area
    {Ω Λ : Type*} {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (B : OriginalBorelStripFamily (originalJointPositiveWidthDomain ρ))
    (H K N : ℕ) (C : ℝ)
    (hB : ∀ p, (projectionFiber (D.part i) p.val).Nonempty → B.ComponentStripAt D i H K N C p)
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) {ω : Ω} {j : Λ} {k : ℤ}
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (hT : 0≤radius ω) (ho : IsOpen E)
    (hbounded : Bornology.IsBounded E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω)) :
    let p := originalDyadicPositiveParameters param radius k ω
    let W := (2:ℝ)^k
    let L := originalJointComponentScale D i p.val
    let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (B.anchor p)
    let a := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)
    let S := B.strip p W
    S⊆E ∧ L*W/(8*(H : ℝ)*(K : ℝ))≤volume.real S ∧
      bufferedBandComponent E W z ∪ S⊆Metric.closedBall a (2*L) ∧
      volume (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S))≤ENNReal.ofReal (4*Real.pi*L^2) ∧
      volume (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S))≠⊤ ∧
      volume.real (relativePlanarEndpoints a (bufferedBandComponent E W z ∪ S))≤4*Real.pi*L^2 := by
  let p := originalDyadicPositiveParameters param radius k ω
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (B.anchor p)
  rcases originalDyadicComponentAssigned_common_strip D i B H K N C hB active param radius point hj
    with ⟨ha,_,_,_,hgeom⟩
  rcases hgeom E hT ho hbounded hE hbox with ⟨hsub,_,_,hlower,hcontrol⟩
  change BufferedBandEndpointControl E ((2:ℝ)^k) z (B.strip p ((2:ℝ)^k)) at hcontrol
  have hz : (WithLp.equiv 2 (Fin 2 → ℝ)) z∈projectionFiber (D.part i) p.val := by
    simpa only [z,Equiv.apply_symm_apply] using ha
  have hW : 0<(2:ℝ)^k := zpow_pos (by norm_num) k
  have hpoint := originalJointEndpoint_mem_actual_component D (param ω) hT hW ho hE hbox i z hz hj.2
  have hscale := originalJointComponentScale_eq D (param ω) hT hW ho hE hbox i z hz
  change originalJointComponentScale D i p.val=bufferedComponentScale E ((2:ℝ)^k) z at hscale
  have hbound := hcontrol _ hpoint
  rw [← hscale] at hbound
  exact ⟨hsub,hlower,hbound⟩

end PaperI
