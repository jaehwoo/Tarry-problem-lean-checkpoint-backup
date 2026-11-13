import PaperILean.OriginalOccupiedPlanarGeometry

noncomputable section
namespace PaperI

open Set MeasureTheory
open scoped ENNReal

universe u v

/-- Paper I I3217 with the same I1242 assignment and physical centerline. -/
theorem derivative_good_points_curved_strips
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (hMono : PublishedOneVariableMonotonicity) (s d N : ℕ) (c r : ℝ) :
    ∃ Nc H K m : ℕ, 2≤H ∧ 0<K ∧ 0<m ∧ ∃ C : ℝ, 1≤C ∧
      ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count≤Nc ∧
        ∃ B : Fin D.count → OriginalBorelStripFamily
          (originalJointPositiveWidthDomain (Fin s × (Fin 2 → Fin (d+1)))),
        (∀ (i : Fin D.count) p, (projectionFiber (D.part i) p.val).Nonempty →
          (B i).ComponentStripAt D i H K N C p ∧
          ∀ P : ℝ, 2≤P → P^(-c)/2≤p.val (Sum.inr ()) → (B i).RoundedComponentAt D i N (P^m) p) ∧
        ∀ (Ω : Type u) (Λ : Type v) (active : Ω → Λ → Prop)
          (param : Ω → (Fin s × (Fin 2 → Fin (d+1))) → ℝ) (radius : Ω → ℝ)
          (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
          (E : Set (WithLp 2 (Fin 2 → ℝ))),
          IsOpen E → Bornology.IsBounded E → 0≤radius ω →
          (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber (universalPolynomialBooleanSet (Fin 2) s d b) (param ω) →
          (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox (radius ω) →
          ∀ P mass : ℝ, 2≤P →
          (∀ j, active ω j → P^(-c)≤Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
          (∀ u : Fin 2 → ℝ,
            {j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.Finite ∧
            ({j | active ω j ∧ (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)∈planarSquare u (P^(-c))}.ncard : ℝ)≤P^r*mass) →
          OriginalDyadicPackingBounds D active param radius point ω m P mass ∧
          ∀ (j : Λ) (k : ℤ) (i : Fin D.count),
            originalDyadicComponentAssigned D active param radius point ω j k i →
            let p := originalDyadicPositiveParameters param radius k ω
            let L := roundedDyadicScale (originalJointComponentScale D i p.val)
            let W := roundedDyadicScale ((2:ℝ)^k)
            let I := {j' | originalDyadicComponentAssigned D active param radius point ω j' k i}
            let S := originalAssignedPlanarStrip D B active param radius point ω j
            let J := Icc ((B i).left p) ((B i).right p)
            let ζ := fun x => (B i).graph (p,x)
            Metric.diam ((fun j' => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j')) '' I) ≤ L ∧
              1 ≤ W ∧ W ≤ L ∧
              S ⊆ E ∧ MeasurableSet S ∧ L * W / P^m ≤ volume.real S ∧
              (∀ j'∈I, originalAssignedPlanarStrip D B active param radius point ω j' = S) ∧
              AnalyticOnNhd ℝ ζ J ∧
              (∀ x∈J, ∀ n, 0<n → n≤N → |iteratedDeriv n ζ x| ≤ P^m * L / L^n) ∧
              (∀ s₀∈J, ∀ x∈J, |ζ x - ζ s₀| ≤ P^(m+1) * L) := by
  obtain ⟨Nc,H,K,m,hH,hK,hm,C,hC,hbase⟩ :=
    published_inputFormat_original_planar_strip_package hDD hCAD hCell hHardt hQE hPiece hMono s d N c r
  refine ⟨Nc,H,K,m,hH,hK,hm,C,hC,?_⟩
  intro b
  obtain ⟨D,hD,B,hB,hpack⟩ := hbase b
  refine ⟨D,hD,B,hB,?_⟩
  intro Ω Λ active param radius point ω E ho hb hT hE hbox P mass hP hbuffer hlocal
  have hpacking := hpack Ω Λ active param radius point ω E ho hb hT hE hbox P mass hP hbuffer hlocal
  refine ⟨hpacking,?_⟩
  intro j k i hj
  let p := originalDyadicPositiveParameters param radius k ω
  let L := roundedDyadicScale (originalJointComponentScale D i p.val)
  have hnonempty : (projectionFiber (D.part i) p.val).Nonempty := ⟨point ω j,hj.2⟩
  have hcomp := (hB i p hnonempty).1
  have hrounded := originalDyadicAssigned_rounded_strip D i (B i) N m c
    (fun p hp P hP hwidth => (hB i p hp).2 P hP hwidth)
    active param radius point ho hT hE hbox P hP (hbuffer j hj.1.1) hj
  obtain ⟨_,_,hdiam,hW,hWL,hprep,_,_,_,_,hSE,hSm,_,harea,hcommon⟩ :=
    originalDyadicAssigned_common_rounded_geometry D B active param radius point ω j k i
      H K N m C P mass hpacking hj hcomp hrounded ho hb hT hE hbox
  rcases hprep with ⟨_,hanalytic,hcenter,hpos⟩
  refine ⟨hdiam,hW,hWL,hSE,hSm,harea,fun j' hj' => (hcommon j' hj').1,
    hanalytic,hpos,?_⟩
  intro s₀ hs₀ x hx
  let ζ : ℝ → ℝ := fun t => (B i).graph (p,t)
  let z₀ := ζ ((B i).reference p)
  have hs : |ζ s₀-z₀| ≤ P^m*L := by
    simpa only [iteratedDeriv_zero,pow_zero,div_one] using hcenter s₀ hs₀ 0 (Nat.zero_le N)
  have ht : |ζ x-z₀| ≤ P^m*L := by
    simpa only [iteratedDeriv_zero,pow_zero,div_one] using hcenter x hx 0 (Nat.zero_le N)
  change |ζ x-ζ s₀| ≤ _
  calc
    |ζ x-ζ s₀| ≤ |ζ x-z₀| + |ζ s₀-z₀| := by
      simpa only [abs_sub_comm z₀ (ζ s₀)] using abs_sub_le (ζ x) z₀ (ζ s₀)
    _ ≤ P^m*L + P^m*L := add_le_add ht hs
    _ ≤ P^(m+1)*L := by
      rw [pow_succ]
      have hL : 0≤L := (roundedDyadicScale_pos _).le
      have hPL : 0 ≤ P^m*L := mul_nonneg (pow_nonneg (show 0 ≤ P by linarith) m) hL
      calc
        _ = (P^m*L)*2 := by ring
        _ ≤ (P^m*L)*P := mul_le_mul_of_nonneg_left hP hPL
        _ = _ := by ring

end PaperI
