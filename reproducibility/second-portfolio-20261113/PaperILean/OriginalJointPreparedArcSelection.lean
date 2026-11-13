import PaperILean.OriginalSelectedArcPreparation
import PaperILean.JointOriginalMacroscopicArc
import PaperILean.JointPreparationFormatUniformity

/-! I1263/I1265: preparation on the actual first-maximum arc of the original
joint cut path. The same directions, graphs and maximum are retained. -/
noncomputable section
namespace PaperI
open Set

structure OriginalJointPreparedArcData {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℝ → Fin 2 → ℝ) (H : ℕ) (n : Ω → ℕ) (t : Ω → ℕ → ℝ)
    (L : Ω → ℝ) (N : ℕ) (C : ℝ) (K : ℕ) where
  direction : Ω × ℕ → Fin 4
  graph : (Ω × ℕ) × ℝ → ℝ
  index : Ω → ℕ
  left : Ω → ℝ
  right : Ω → ℝ
  measurable_direction : Measurable direction
  measurable_graph : Measurable graph
  measurable_index : Measurable index
  measurable_time_left : Measurable (fun ω => t ω (index ω))
  measurable_time_right : Measurable (fun ω => t ω (index ω+1))
  measurable_selected_direction : Measurable (fun ω => direction (ω,index ω))
  measurable_selected_graph : Measurable (fun v : Ω × ℝ => graph ((v.1,index v.1),v.2))
  measurable_left : Measurable left
  measurable_right : Measurable right
  arcs : ∀ ω j, SelectedOriginalPlanarArc (g ω) (t ω j) (t ω (j+1))
    (direction (ω,j)) (fun x => graph ((ω,j),x))
  maximum : ∀ ω, PrefixMaximum (originalArcWidth (g ω) (t ω)
    (fun j => direction (ω,j))) (n ω) (index ω)
  first_maximum : ∀ ω j, j < index ω →
    originalArcWidth (g ω) (t ω) (fun r => direction (ω,r)) j <
      originalArcWidth (g ω) (t ω) (fun r => direction (ω,r)) (index ω)
  endpoint_distance : ∀ ω,
    dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g ω 0))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g ω 1)) ≤
        2*(H : ℝ)*originalArcWidth (g ω) (t ω) (fun j => direction (ω,j)) (index ω)
  span : ∀ ω, L ω/(4*(H : ℝ)) ≤
    originalArcWidth (g ω) (t ω) (fun j => direction (ω,j)) (index ω)
  prepared : ∀ ω, OriginalPreparedGraphInterval (fun x => graph ((ω,index ω),x))
    (planarDirectionSign (direction (ω,index ω))*
      g ω (t ω (index ω)) (planarDirectionI (direction (ω,index ω))))
    (planarDirectionSign (direction (ω,index ω))*
      g ω (t ω (index ω+1)) (planarDirectionI (direction (ω,index ω))))
    (left ω) (right ω) C K N
  macroscopic_length : ∀ ω, L ω/(4*(H : ℝ)*(K : ℝ)) ≤ right ω-left ω

theorem published_joint_original_prepared_arc_selection
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g)) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (q : Ω → P), Measurable q →
      ∀ (H : ℕ) (n : Ω → ℕ) (t : Ω → ℕ → ℝ),
      Measurable n → (∀ j, Measurable (fun ω => t ω j)) →
      (∀ ω, OriginalPlanarReadoutPartition (g (q ω).val) H (n ω) (t ω)) →
      (∀ ω, ContinuousOn (g (q ω).val) (Icc (0:ℝ) 1)) →
      ∀ L : Ω → ℝ, (∀ ω, 0<L ω) →
      (∀ ω, L ω/2 ≤ dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (q ω).val 0))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (q ω).val 1))) →
      Nonempty (OriginalJointPreparedArcData (fun ω => g (q ω).val) H n t L N C K) := by
  obtain ⟨S⟩ := published_original_joint_arc_selector_family hCAD hQE hHardt hg
  obtain ⟨C,hC,K,hK,hprep⟩ := S.prepare_selected_arcs hDD hCAD hCell hHardt hQE hPiece hg N
  refine ⟨C,hC,K,hK,?_⟩
  intro Ω inst q hq H n t hn ht hpart hc L hL hsep
  obtain ⟨d,F,k,hd,hF,hk,hleft,hright,hdir,hgraph,hsel⟩ :=
    published_joint_original_macroscopic_arc hCAD hQE hHardt hg q hq H n t hn ht hpart hc
  have hH (ω) : 0<H := (hpart ω).1.trans_le (hpart ω).2.1
  have hwidth (ω) : L ω/(4*(H : ℝ)) ≤
      originalArcWidth (g (q ω).val) (t ω) (fun j => d (ω,j)) (k ω) :=
    selected_original_prefixMaximum_half_separation (hpart ω) _ _
      (fun j _ => (hsel ω).1 j) (hsel ω).2.1 (hsep ω)
  have hall (ω) := (hpart ω).all_intervals (hc ω) (k ω)
  obtain ⟨u,v,hu,hv,hprepared⟩ := hprep Ω q
    (fun ω => t ω (k ω)) (fun ω => t ω (k ω+1))
    (fun ω => d (ω,k ω)) (fun ω x => F ((ω,k ω),x))
    hq hleft hright hdir (fun ω => (hall ω).1) (fun ω => (hall ω).2.1)
    (fun ω => (hall ω).2.2.1) (fun ω => (hsel ω).1 (k ω))
    (fun ω => by
      apply sub_pos.mp
      change 0<originalArcWidth (g (q ω).val) (t ω) (fun j => d (ω,j)) (k ω)
      exact (div_pos (hL ω) (mul_pos (by norm_num) (by exact_mod_cast hH ω))).trans_le (hwidth ω))
  refine ⟨⟨d,F,k,u,v,hd,hF,hk,hleft,hright,hdir,hgraph,hu,hv,
    fun ω => (hsel ω).1,fun ω => (hsel ω).2.1,fun ω => (hsel ω).2.2.1,
    fun ω => (hsel ω).2.2.2,hwidth,hprepared,?_⟩⟩
  intro ω
  exact prepared_interval_macroscopic_length (hH ω) hK (hwidth ω) (hprepared ω).2.2.1

end PaperI
