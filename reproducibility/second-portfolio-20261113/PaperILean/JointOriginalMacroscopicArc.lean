import PaperILean.JointOriginalArcData

/-! I1263/I1265: apply the checked fixed-tie maximum to the actual widths
of the jointly selected original arcs. H bounds active INTERVALS n<=H.
The polygon inequality is the original argument, now with the selected data. -/
noncomputable section
namespace PaperI
open Set

def originalArcWidth (g : ℝ → Fin 2 → ℝ) (t : ℕ → ℝ) (d : ℕ → Fin 4) (j : ℕ) : ℝ :=
  planarDirectionSign (d j)*g (t (j+1)) (planarDirectionI (d j)) -
    planarDirectionSign (d j)*g (t j) (planarDirectionI (d j))

theorem SelectedOriginalPlanarArc.width_nonneg
    {g : ℝ → Fin 2 → ℝ} {a b : ℝ} {d : Fin 4} {F : ℝ → ℝ}
    (h : SelectedOriginalPlanarArc g a b d F) (hab : a≤b) :
    0 ≤ planarDirectionSign d*g b (planarDirectionI d) -
      planarDirectionSign d*g a (planarDirectionI d) :=
  sub_nonneg.mpr (h.1.2.2.1 ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)

theorem SelectedOriginalPlanarArc.width_eq_abs
    {g : ℝ → Fin 2 → ℝ} {a b : ℝ} {d : Fin 4} {F : ℝ → ℝ}
    (h : SelectedOriginalPlanarArc g a b d F) (hab : a≤b) :
    planarDirectionSign d*g b (planarDirectionI d) -
      planarDirectionSign d*g a (planarDirectionI d) =
      |g b (planarDirectionI d)-g a (planarDirectionI d)| := by
  rw [← abs_of_nonneg (h.width_nonneg hab)]
  rcases planarDirection_sign d with hs | hs
  · simp only [hs,one_mul]
  · simp only [hs,neg_one_mul,neg_sub_neg,abs_sub_comm]

theorem selected_original_prefixMaximum_span
    {g : ℝ → Fin 2 → ℝ} {H n : ℕ} {t : ℕ → ℝ}
    (hpart : OriginalPlanarReadoutPartition g H n t)
    (d : ℕ → Fin 4) (F : ℕ → ℝ → ℝ)
    (harc : ∀ j<n, SelectedOriginalPlanarArc g (t j) (t (j+1)) (d j) (F j))
    {k : ℕ} (hmax : PrefixMaximum (originalArcWidth g t d) n k) :
    dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 0))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 1)) ≤
      2*(H:ℝ)*originalArcWidth g t d k := by
  have hab (j : ℕ) (hj : j<n) := (hpart.2.2.2.2.2.2 j hj).2.2.1.le
  have hend (c : Fin 2) : |g (t 0) c-g (t n) c| ≤ (n:ℝ)*originalArcWidth g t d k := by
    have hb : ∀ {r : ℕ}, r<n → dist (g (t r) c) (g (t (r+1)) c) ≤ originalArcWidth g t d k := by
      intro r hr
      have hu : t r∈Icc (t r) (t (r+1)) := ⟨le_rfl,hab r hr⟩
      have hv : t (r+1)∈Icc (t r) (t (r+1)) := ⟨hab r hr,le_rfl⟩
      have hd := (harc r hr).1.2.2.2.1 (t r) hu (t (r+1)) hv c
      have hw : originalArcWidth g t d r = |g (t (r+1)) (planarDirectionI (d r))-
          g (t r) (planarDirectionI (d r))| := (harc r hr).width_eq_abs (hab r hr)
      have hs : dist (g (t r) c) (g (t (r+1)) c) ≤ originalArcWidth g t d r := by
        rw [hw,Real.dist_eq,abs_sub_comm]
        simpa only [abs_sub_comm] using hd
      exact hs.trans (hmax.2 r hr)
    simpa only [Real.dist_eq,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
      dist_le_range_sum_of_dist_le (f := fun r => g (t r) c) n hb
  have hdist := planar_euclidean_dist_le_coordinate_sum (g (t 0)) (g (t n))
  have hsmall : dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (t 0)))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (t n))) ≤
      2*(n:ℝ)*originalArcWidth g t d k := by linarith [hend 0,hend 1]
  rw [hpart.2.2.1,hpart.2.2.2.1] at hsmall
  apply hsmall.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hpart.2.1)
    (by norm_num)) ((harc k hmax.1).width_nonneg (hab k hmax.1))

theorem selected_original_prefixMaximum_half_separation
    {g : ℝ → Fin 2 → ℝ} {H n : ℕ} {t : ℕ → ℝ}
    (hpart : OriginalPlanarReadoutPartition g H n t)
    (d : ℕ → Fin 4) (F : ℕ → ℝ → ℝ)
    (harc : ∀ j<n, SelectedOriginalPlanarArc g (t j) (t (j+1)) (d j) (F j))
    {k : ℕ} (hmax : PrefixMaximum (originalArcWidth g t d) n k)
    {L : ℝ} (hsep : L/2 ≤ dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 0))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g 1))) :
    L/(4*(H:ℝ)) ≤ originalArcWidth g t d k := by
  have hH : 0 < (H:ℝ) := by exact_mod_cast hpart.1.trans_le hpart.2.1
  apply (div_le_iff₀ (by positivity : 0 < 4*(H:ℝ))).mpr
  have hs := selected_original_prefixMaximum_span hpart d F harc hmax
  nlinarith

theorem published_measurable_actual_original_widths
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (q : Ω → P) (hq : Measurable q)
    (t : Ω → ℕ → ℝ) (ht : ∀ j, Measurable (fun ω => t ω j))
    (htU : ∀ ω j, t ω j∈Icc (0:ℝ) 1)
    (d : Ω × ℕ → Fin 4) (hd : Measurable d) :
    ∀ j, Measurable (fun ω => originalArcWidth (g (q ω).val) (t ω) (fun r => d (ω,r)) j) := by
  have heval (j : ℕ) : Measurable (fun ω => g (q ω).val (t ω j)) := by
    have htime : Measurable (fun ω => (⟨t ω j,htU ω j⟩ : Icc (0:ℝ) 1)) := (ht j).subtype_mk
    exact (published_jointUnitPath_measurable hQE hHardt hg).comp (hq.prodMk htime)
  intro j
  have hdir : Measurable (fun ω => d (ω,j)) := hd.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun v : Ω × Fin 4 =>
      planarDirectionSign v.2*g (q v.1).val (t v.1 (j+1)) (planarDirectionI v.2)-
      planarDirectionSign v.2*g (q v.1).val (t v.1 j) (planarDirectionI v.2)) := by
    apply measurable_from_prod_countable
    intro c
    exact (((measurable_pi_apply _).comp (heval (j+1))).const_mul _).sub
      (((measurable_pi_apply _).comp (heval j)).const_mul _)
  exact hm.comp (measurable_id.prodMk hdir)

theorem published_joint_original_macroscopic_arc
    (hCAD : PublishedCylindricalInitialBandDecomposition)
    (hQE : PublishedRealSemialgebraicity) (hHardt : PublishedSemialgebraicHardtTriviality)
    {α : Type} [Finite α] {P : Set (α → ℝ)} {g : (α → ℝ) → ℝ → Fin 2 → ℝ}
    (hg : HasPolynomialSignDescription (jointUnitPathGraph P g))
    {Ω : Type*} [MeasurableSpace Ω] (q : Ω → P) (hq : Measurable q)
    (H : ℕ) (n : Ω → ℕ) (t : Ω → ℕ → ℝ)
    (hn : Measurable n) (ht : ∀ j, Measurable (fun ω => t ω j))
    (hpart : ∀ ω, OriginalPlanarReadoutPartition (g (q ω).val) H (n ω) (t ω))
    (hc : ∀ ω, ContinuousOn (g (q ω).val) (Icc (0:ℝ) 1)) :
    ∃ (d : Ω × ℕ → Fin 4) (F : (Ω × ℕ) × ℝ → ℝ) (k : Ω → ℕ),
      Measurable d ∧ Measurable F ∧ Measurable k ∧
      Measurable (fun ω => t ω (k ω)) ∧ Measurable (fun ω => t ω (k ω+1)) ∧
      Measurable (fun ω => d (ω,k ω)) ∧ Measurable (fun v : Ω × ℝ => F ((v.1,k v.1),v.2)) ∧
      ∀ ω, (∀ j, SelectedOriginalPlanarArc (g (q ω).val) (t ω j) (t ω (j+1))
        (d (ω,j)) (fun x => F ((ω,j),x))) ∧
        PrefixMaximum (originalArcWidth (g (q ω).val) (t ω) (fun j => d (ω,j))) (n ω) (k ω) ∧
        (∀ j<k ω, originalArcWidth (g (q ω).val) (t ω) (fun r => d (ω,r)) j <
          originalArcWidth (g (q ω).val) (t ω) (fun r => d (ω,r)) (k ω)) ∧
        dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (q ω).val 0))
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (g (q ω).val 1)) ≤
          2*(H:ℝ)*originalArcWidth (g (q ω).val) (t ω) (fun r => d (ω,r)) (k ω) := by
  obtain ⟨d,F,hd,hF,hdata⟩ := published_joint_original_partition_arc_data hCAD hQE hHardt
    hg q hq H n t ht hpart hc
  let w := fun ω => originalArcWidth (g (q ω).val) (t ω) (fun j => d (ω,j))
  have hw := published_measurable_actual_original_widths hQE hHardt hg q hq t ht
    (fun ω j => ((hpart ω).all_intervals (hc ω) j).1) d hd
  let k := fun ω => firstPrefixMaximum (w ω) (hpart ω).1
  have hk : Measurable k := measurable_firstPrefixMaximum w n hw hn (fun ω => (hpart ω).1)
  have hpair : Measurable (fun ω => (ω,k ω)) := measurable_id.prodMk hk
  have htall : Measurable (fun v : Ω × ℕ => t v.1 v.2) := measurable_from_prod_countable ht
  refine ⟨d,F,k,hd,hF,hk,htall.comp hpair,?_,hd.comp hpair,?_,?_⟩
  · have hsucc : Measurable (fun v : Ω × ℕ => t v.1 (v.2+1)) :=
      measurable_from_prod_countable (fun j => ht (j+1))
    exact hsucc.comp hpair
  · exact hF.comp ((hpair.comp measurable_fst).prodMk measurable_snd)
  · intro ω
    have hs := firstPrefixMaximum_spec (w ω) (hpart ω).1
    exact ⟨fun j => (hdata ω j).1,hs,
      fun j hj => firstPrefixMaximum_strict_before (w ω) (hpart ω).1 hj,
      selected_original_prefixMaximum_span (hpart ω) _ _ (fun j _ => (hdata ω j).1) hs⟩

end PaperI
