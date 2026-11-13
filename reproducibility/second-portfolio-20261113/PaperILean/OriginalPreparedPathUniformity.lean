import PaperILean.OriginalJointPreparedArcSelection
import PaperILean.OriginalJointEndpointCutPaths

/-! Original I654/I1263/I1265: retain the joint cut path together with its
prepared selected-arc application. Universal input families and finite sums
place the common constants before all Boolean tables and coefficient values. -/
noncomputable section
universe u
namespace PaperI
open Set

theorem OriginalPreparedGraphInterval.mono
    {f : ℝ → ℝ} {a b u v C C' : ℝ} {K K' N : ℕ}
    (h : OriginalPreparedGraphInterval f a b u v C K N)
    (hC : C≤C') (hK : K≤K') (hKpos : 0<K) :
    OriginalPreparedGraphInterval f a b u v C' K' N := by
  have hab : a≤b := by
    have hx := h.2.1 (left_mem_Icc.mpr h.1.le)
    exact hx.1.trans hx.2
  have hlen : (b-a)/(K' : ℝ)≤v-u :=
    (div_le_div_of_nonneg_left (sub_nonneg.mpr hab)
      (by exact_mod_cast hKpos) (by exact_mod_cast hK)).trans h.2.2.1
  have hbound (n : ℕ) : C*(b-a)/(b-a)^n≤C'*(b-a)/(b-a)^n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sub_nonneg.mpr hab))
      (pow_nonneg (sub_nonneg.mpr hab) n)
  exact ⟨h.1,h.2.1,hlen,h.2.2.2.1,
    fun x hx n hn => (h.2.2.2.2.1 x hx n hn).trans (hbound n),
    fun x hx n hn hN => (h.2.2.2.2.2 x hx n hn hN).trans (hbound n)⟩

def OriginalJointPreparedArcData.rebound
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → Fin 2 → ℝ}
    {H : ℕ} {n : Ω → ℕ} {t : Ω → ℕ → ℝ} {L : Ω → ℝ}
    {N K K' : ℕ} {C C' : ℝ}
    (D : OriginalJointPreparedArcData g H n t L N C K)
    (hC : C≤C') (hK : K≤K') (hKpos : 0<K) (hH : ∀ ω : Ω, 0<H) :
    OriginalJointPreparedArcData g H n t L N C' K' where
  direction := D.direction
  graph := D.graph
  index := D.index
  left := D.left
  right := D.right
  measurable_direction := D.measurable_direction
  measurable_graph := D.measurable_graph
  measurable_index := D.measurable_index
  measurable_time_left := D.measurable_time_left
  measurable_time_right := D.measurable_time_right
  measurable_selected_direction := D.measurable_selected_direction
  measurable_selected_graph := D.measurable_selected_graph
  measurable_left := D.measurable_left
  measurable_right := D.measurable_right
  arcs := D.arcs
  maximum := D.maximum
  first_maximum := D.first_maximum
  endpoint_distance := D.endpoint_distance
  span := D.span
  prepared := fun ω => (D.prepared ω).mono hC hK hKpos
  macroscopic_length := fun ω => prepared_interval_macroscopic_length
    (hH ω) (hKpos.trans_le hK) (D.span ω)
    ((D.prepared ω).mono hC hK hKpos).2.2.1

structure OriginalPreparedJointPathFamily {ρ : Type}
    (P : Set (ρ → ℝ)) (S : Set ((ρ ⊕ Fin 2) → ℝ))
    (s d H N : ℕ) (C : ℝ) (K : ℕ) where
  path : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℝ → Fin 2 → ℝ
  activeCount : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℕ
  cuts : (((ρ ⊕ Fin 2) ⊕ Fin 2) → ℝ) → ℕ → ℝ
  joint_graph : HasPolynomialSignDescription (jointUnitPathGraph (cellChainEndpointDomain P S) path)
  measurable_count : Measurable activeCount
  measurable_cuts : ∀ j, Measurable (fun q => cuts q j)
  paths : ∀ p∈P, ∀ a∈projectionFiber S p, ∀ b∈projectionFiber S p,
    ∃ γ : SemialgebraicUnitPath (projectionFiber S p) a b,
      γ.toFun=path (Sum.elim (Sum.elim p a) b) ∧
      ∃ A : Finset (MvPolynomial (Unit ⊕ Fin 2) ℝ), A.card≤s ∧
        (∀ q∈A, q.totalDegree≤d) ∧ PolynomialSignDetermined A (unitPathGraph γ.toFun)
  partition : ∀ q∈cellChainEndpointDomain P S,
    OriginalPlanarReadoutPartition (path q) H (activeCount q) (cuts q)
  prepare : ∀ (Ω : Type u) [MeasurableSpace Ω]
    (q : Ω → cellChainEndpointDomain P S), Measurable q →
    ∀ L : Ω → ℝ, (∀ ω, 0<L ω) →
    (∀ ω, L ω/2 ≤ dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (path (q ω).val 0))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (path (q ω).val 1))) →
    Nonempty (OriginalJointPreparedArcData (fun ω => path (q ω).val) H
      (fun ω => activeCount (q ω).val) (fun ω => cuts (q ω).val) L N C K)

theorem OriginalPreparedJointPathFamily.forget {ρ : Type}
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)} {s d H N K : ℕ} {C : ℝ}
    (F : OriginalPreparedJointPathFamily P S s d H N C K) :
    OriginalJointEndpointCutPathFamily P S s d H :=
  ⟨F.path,F.activeCount,F.cuts,F.joint_graph,F.measurable_count,F.measurable_cuts,F.paths,F.partition⟩

theorem OriginalPreparedJointPathFamily.mono {ρ : Type}
    {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)}
    {s d H N K K' : ℕ} {C C' : ℝ}
    (F : OriginalPreparedJointPathFamily.{u} P S s d H N C K)
    (hC : C≤C') (hK : K≤K') (hKpos : 0<K) :
    Nonempty (OriginalPreparedJointPathFamily.{u} P S s d H N C' K') := by
  refine ⟨⟨F.path,F.activeCount,F.cuts,F.joint_graph,F.measurable_count,
    F.measurable_cuts,F.paths,F.partition,?_⟩⟩
  intro Ω inst q hq L hL hsep
  obtain ⟨D⟩ := F.prepare Ω q hq L hL hsep
  exact ⟨D.rebound hC hK hKpos
    (fun ω => (F.partition (q ω).val (q ω).property).1.trans_le
      (F.partition (q ω).val (q ω).property).2.1)⟩

theorem published_original_joint_cut_path_preparation
    (hDD : PublishedEquispacedDividedDifferenceMeanValue)
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hCell : PublishedFiniteConnectedCover) (hHardt : PublishedSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity) (hPiece : PublishedPiecewiseNashExtensions)
    {ρ : Type} [Finite ρ] {P : Set (ρ → ℝ)} {S : Set ((ρ ⊕ Fin 2) → ℝ)}
    {s d H : ℕ} (h : OriginalJointEndpointCutPathFamily P S s d H) (N : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∃ K : ℕ, 0<K ∧
      Nonempty (OriginalPreparedJointPathFamily.{u} P S s d H N C K) := by
  obtain ⟨g,n,t,hg,hn,ht,hpath,hpart⟩ := h
  obtain ⟨C,hC,K,hK,hprep⟩ := published_joint_original_prepared_arc_selection
    hDD hCAD hCell hHardt hQE hPiece hg N
  refine ⟨C,hC,K,hK,⟨g,n,t,hg,hn,ht,hpath,hpart,?_⟩⟩
  intro Ω inst q hq L hL hsep
  apply hprep Ω q hq H _ _ (hn.comp (measurable_subtype_coe.comp hq))
    (fun j => (ht j).comp (measurable_subtype_coe.comp hq))
    (fun ω => hpart (q ω).val (q ω).property) _ L hL hsep
  intro ω
  let p : ρ → ℝ := fun r => (q ω).val (Sum.inl (Sum.inl r))
  let a : Fin 2 → ℝ := fun k => (q ω).val (Sum.inl (Sum.inr k))
  let b : Fin 2 → ℝ := fun k => (q ω).val (Sum.inr k)
  have he : Sum.elim (Sum.elim p a) b=(q ω).val := by
    funext i
    rcases i with (r | k) | k <;> rfl
  obtain ⟨γ,hγ,_⟩ := hpath p (q ω).property.1 a (q ω).property.2.1 b (q ω).property.2.2
  rw [he] at hγ
  rw [← hγ]
  exact γ.continuousOn

theorem published_inputFormat_original_prepared_cut_paths
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
          Nonempty (OriginalPreparedJointPathFamily.{u} univ (D.part i) sPath dPath H N C K) := by
  classical
  obtain ⟨Nc,sp,dp,H,hH,h⟩ := published_inputFormat_original_joint_readout_cut_paths
    hCAD hCell hHardt hQE hPiece s d
  choose D hcount hpath using h
  let B := (Fin s → Bool × Bool) → Bool
  have hi (b : B) (i : Fin (D b).count) := published_original_joint_cut_path_preparation
    hDD hCAD hCell.toFiniteConnectedCover hHardt.toHardtTriviality hQE hPiece (hpath b i) N
  choose C hC K hK data using hi
  let I := (b : B) × Fin (D b).count
  let CT : ℝ := 1+∑ u : I, C u.1 u.2
  let KT : ℕ := 1+∑ u : I, K u.1 u.2
  have hCb (b : B) (i : Fin (D b).count) : C b i≤CT := by
    have hs : C b i≤∑ u : I, C u.1 u.2 := Finset.single_le_sum
      (fun (u : I) _ => zero_le_one.trans (hC u.1 u.2)) (Finset.mem_univ (⟨b,i⟩ : I))
    dsimp [CT]
    linarith
  have hKb (b : B) (i : Fin (D b).count) : K b i≤KT := by
    have hs : K b i≤∑ u : I, K u.1 u.2 := Finset.single_le_sum (f := fun u : I => K u.1 u.2)
      (fun (u : I) _ => Nat.zero_le _) (Finset.mem_univ (⟨b,i⟩ : I))
    dsimp [KT]
    omega
  have hCT : 1≤CT := by
    have hs : 0≤∑ u : I, C u.1 u.2 := Finset.sum_nonneg (fun u _ => zero_le_one.trans (hC u.1 u.2))
    dsimp [CT]
    linarith
  have hKT : 0<KT := by dsimp [KT]; omega
  refine ⟨Nc,sp,dp,H,hH,CT,hCT,KT,hKT,?_⟩
  intro b
  refine ⟨D b,hcount b,?_⟩
  intro i
  obtain ⟨F⟩ := data b i
  exact F.mono (hCb b i) (hKb b i) (hK b i)

end PaperI
