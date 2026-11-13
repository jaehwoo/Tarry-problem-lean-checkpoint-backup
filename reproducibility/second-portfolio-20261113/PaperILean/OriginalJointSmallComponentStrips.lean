import PaperILean.OriginalPreparedComponentStrips

/-! Original I1263 small branch: one common Borel center per catalogue entry,
chosen before original labels, and the same concrete constant-centerline strip. -/
noncomputable section
namespace PaperI
open Set MeasureTheory

theorem published_original_joint_component_center
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {ρ : Type} [Finite ρ] {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count) :
    ∃ x : ((((ρ ⊕ Unit) ⊕ Unit) → ℝ)) → Fin 2 → ℝ,
      Measurable x ∧ HasPolynomialSignDescription (selectedFunctionGraph univ x) ∧
      ∀ p, (projectionFiber (D.part i) p).Nonempty → x p∈projectionFiber (D.part i) p := by
  obtain ⟨x,hx,hxs,hmem⟩ := published_joint_vector_selector hCAD hQE hHardt
    (D.part i) (hasPolynomialSignDescription_definable (D.semialgebraic i))
  refine ⟨x,hx,hxs,?_⟩
  intro p hp
  exact hmem p hp

theorem original_joint_small_rectangle_geometry
    {ρ : Type} {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G)) (i : Fin D.count)
    (p : ρ → ℝ) {T W : ℝ} (hT : 0≤T) (hW : 0<W)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E) (hbounded : Bornology.IsBounded E)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E=projectionFiber G p)
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E⊆planarCoordinateBox T)
    (x : Fin 2 → ℝ)
    (hx : x∈projectionFiber (D.part i) (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)))
    (hsmall : planarFiberDiameter (D.part i)
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))≤W) :
    let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm x
    let R := bufferedPointRectangle z W
    originalJointComponentScale D i (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))=W ∧
      R⊆E ∧ MeasurableSet R ∧
      volume.real R=originalJointComponentScale D i
        (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))*W/4 ∧
      BufferedBandEndpointControl E W z R := by
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm x
  have hscale : originalJointComponentScale D i
      (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W))=W := max_eq_left hsmall
  have hxband := D.subset (Sum.elim (Sum.elim p (fun _ => T)) (fun _ => W)) i hx
  rw [originalJointBand_fiber_eq G p hT hW ho hE hbox] at hxband
  have hz : z∈bufferedDistanceBand E W := by
    obtain ⟨y,hy,he⟩ := hxband
    have hez : z=y := by dsimp [z]; rw [← he,Equiv.symm_apply_apply]
    exact hez.symm ▸ hy
  have harea := bufferedPointRectangle_measurable_volume z hW.le
  exact ⟨hscale,bufferedPointRectangle_subset_of_band hz,harea.1,
    by simpa only [hscale] using harea.2,
    bufferedBand_small_rectangle_endpoint_control hbounded hW.le hz⟩

theorem published_inputFormat_original_prepared_components
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    (s d N : ℕ) :
    ∃ Nc sPath dPath H : ℕ, 2≤H ∧ ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ b : (Fin s → Bool × Bool) → Bool,
      ∃ D : JointComponentPartition
        (planarBoundedBandFamily (universalPolynomialBooleanSet (Fin 2) s d b)),
        D.count≤Nc ∧ ∀ i : Fin D.count,
          Nonempty (OriginalPreparedJointPathFamily.{0} univ (D.part i) sPath dPath H N C K) ∧
          ∃ x, Measurable x ∧ HasPolynomialSignDescription (selectedFunctionGraph univ x) ∧
            ∀ p, (projectionFiber (D.part i) p).Nonempty → x p∈projectionFiber (D.part i) p := by
  obtain ⟨Nc,sp,dp,H,hH,C,hC,K,hK,h⟩ :=
    published_inputFormat_original_prepared_cut_paths hDD hCAD hCell hHardt hQE hPiece s d N
  refine ⟨Nc,sp,dp,H,hH,C,hC,K,hK,?_⟩
  intro b
  obtain ⟨D,hcount,hF⟩ := h b
  exact ⟨D,hcount,fun i => ⟨hF i,published_original_joint_component_center
    hCAD hQE hHardt.toHardtTriviality D i⟩⟩

end PaperI
