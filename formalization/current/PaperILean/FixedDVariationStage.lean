import PaperILean.FiniteSignIntegralBounds
import PaperILean.ActualOrderedPathStage
import PaperILean.FixedDBodyControl

/-! I3237[0,119): a fixed-format actual fixed-d component path with
quantitative full augmented variation and actual body-norm integral.
The graph-format, cut and power bounds precede all coefficients and scales. -/
noncomputable section
namespace PaperI.FixedDVariationStage
open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology
open RegularSectionDifferential RegularSectionRates FiniteSignIntegralBounds

theorem fixed_d_norm_majorant {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (t d0 P Cs : ℝ) (hP : 0 < P)
    (hg : HasDerivAt g (deriv g t) t) (hd : ∀ᶠ u in 𝓝 t, g u 3 = d0)
    (hσ : P^(-Cs) ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 (g t))) (Fin.last 4)) :
    coordinateL2Norm (originalAffineBodyCoordinates (g t) (deriv g t)) ≤
      P^Cs * ∑ i : AugmentedCoordinateIndex k,
        |deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) i) t| := by
  have hD := FixedDBodyControl.constant_body_D_eq_zero g (deriv g t) t d0 hg hd
  have hn := FixedDBodyControl.zero_D_norm_coercivity (augmentedPullback S0 (g t))
    (originalAffineBodyCoordinates (g t) (deriv g t)) hD P Cs hP hσ
  have hq := coordinates_hasDerivAt_body S0 g (deriv g t) t hg
  have he (i : AugmentedCoordinateIndex k) :
      deriv (fun u => augmentedStateCoordinates k (augmentedPullback S0 (g u)) i) t =
        (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
          originalAffineBodyCoordinates (g t) (deriv g t)) i :=
    ((hasDerivAt_pi.mp hq) i).deriv
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hP.le _)
  simpa only [he] using originalHaar_coordinateL2Norm_le_sum_abs
    (augmentedOrbitMatrix k (augmentedPullback S0 (g t)) *ᵥ
      originalAffineBodyCoordinates (g t) (deriv g t))

/-- Apply the finite-sign estimates to the literal augmented coordinates and
the literal body. Endpoint and interior-cut derivatives are not assumed. -/
theorem actual_path_bounds {k : ℕ} (S0 : AugmentedState k)
    (g : ℝ → Fin 6 → ℝ) (C : Finset ℝ) (K : ℕ) (d0 P Cs Cw : ℝ)
    (hP : 0 < P) (hC0 : 0 ∈ C) (hC1 : 1 ∈ C)
    (hC : ∀ c ∈ C, c ∈ Icc (0:ℝ) 1) (hK : C.card ≤ K)
    (hc : ContinuousOn g (Icc (0:ℝ) 1))
    (hd : ∀ t ∈ Icc (0:ℝ) 1, g t 3 = d0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, augmentedStateNorm (augmentedPullback S0 (g t)) ≤ P^Cw)
    (hσ : ∀ t ∈ Icc (0:ℝ) 1, P^(-Cs) ≤ descendingSingularValues
      (dComplement (augmentedPullback S0 (g t))) (Fin.last 4))
    (hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      (∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => g t i) (Ioo u v) ∧
        DerivativeSignOn (fun t => g t i) (Ioo u v)) ∧
      (∀ i : AugmentedCoordinateIndex k,
        AnalyticOnNhd ℝ (fun t => augmentedStateCoordinates k
          (augmentedPullback S0 (g t)) i) (Ioo u v) ∧
        DerivativeSignOn (fun t => augmentedStateCoordinates k
          (augmentedPullback S0 (g t)) i) (Ioo u v))) :
    let q := fun (i : AugmentedCoordinateIndex k) t =>
      augmentedStateCoordinates k (augmentedPullback S0 (g t)) i
    let β := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
    let V := 2*(K:ℝ)*(Fintype.card (AugmentedCoordinateIndex k):ℝ)*P^Cw
    (∀ i, BoundedVariationOn (q i) (Icc (0:ℝ) 1)) ∧
      (∑ i, variationOnFromTo (q i) univ 0 1) ≤ V ∧
      IntervalIntegrable (fun t => ∑ i, |deriv (q i) t|) volume 0 1 ∧
      (∫ t in (0:ℝ)..1, ∑ i, |deriv (q i) t|) ≤ V ∧
      IntervalIntegrable (fun t => coordinateL2Norm (β t)) volume 0 1 ∧
      (∫ t in (0:ℝ)..1, coordinateL2Norm (β t)) ≤ P^Cs*V := by
  classical
  let q := fun (i : AugmentedCoordinateIndex k) t =>
    augmentedStateCoordinates k (augmentedPullback S0 (g t)) i
  let β := fun t => originalAffineBodyCoordinates (g t) (deriv g t)
  have hq (i : AugmentedCoordinateIndex k) := scalar_cut_bounds (q i) C 0 1 (P^Cw) K
    hC0 hC1 hC hK (Real.rpow_nonneg hP.le _)
    (SectionIntegralReadouts.jointReadout_continuousOn S0 g (Icc (0:ℝ) 1) hc (.inr i))
    (fun t ht => (abs_le_sqrt_sum_sq
      (augmentedStateCoordinates k (augmentedPullback S0 (g t))) i).trans (hw t ht))
    (fun u hu v hv huv hno =>
      ⟨((hp u hu v hv huv hno).2 i).1.differentiableOn,((hp u hu v hv huv hno).2 i).2⟩)
  have hsum : IntervalIntegrable (fun t => ∑ i, |deriv (q i) t|) volume 0 1 := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => (hq i).2.2.1)
    have he : (∑ i, fun t => |deriv (q i) t|) = (fun t => ∑ i, |deriv (q i) t|) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hbound : (∫ t in (0:ℝ)..1, ∑ i, |deriv (q i) t|) ≤
      2*(K:ℝ)*(Fintype.card (AugmentedCoordinateIndex k):ℝ)*P^Cw := by
    rw [intervalIntegral.integral_finset_sum (fun i _ => (hq i).2.2.1)]
    calc
      _ ≤ ∑ _i : AugmentedCoordinateIndex k, 2*(K:ℝ)*P^Cw :=
        Finset.sum_le_sum (fun i _ => (hq i).2.2.2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hbi := (ActualOrderedPathStage.actual_body_on_pieces g C 0 1 (by norm_num)
    hC0 hC1 hC hc (fun u hu v hv huv hno => (hp u hu v hv huv hno).1)).1
  have hbn : IntervalIntegrable (fun t => coordinateL2Norm (β t)) volume 0 1 :=
    coordinate_norm_integrable β 0 1 hbi
  refine ⟨fun i => (hq i).1,?_,hsum,hbound,hbn,?_⟩
  · calc
      _ ≤ ∑ _i : AugmentedCoordinateIndex k, 2*(K:ℝ)*P^Cw :=
        Finset.sum_le_sum (fun i _ => (hq i).2.1)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  · calc
      _ ≤ ∫ t in (0:ℝ)..1, P^Cs * ∑ i, |deriv (q i) t| := by
        apply integral_mono_off_cuts _ _ C 0 1 (by norm_num) hC0 hC1 hbn (hsum.const_mul _)
        intro t ht htC
        obtain ⟨u,hu,v,hv,huv,htuv,hno⟩ := FinitePieceFTC.point_in_cut_gap C hC0 hC1 ht htC
        have hga : AnalyticOnNhd ℝ g (Ioo u v) :=
          AnalyticOnNhd.pi (fun i => ((hp u hu v hv huv hno).1 i).1)
        have hdLocal : ∀ᶠ r in 𝓝 t, g r 3 = d0 := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
          exact hd r (Ioo_subset_Icc_self hr)
        exact fixed_d_norm_majorant S0 g t d0 P Cs hP
          (hga t htuv).differentiableAt.hasDerivAt hdLocal (hσ t (Ioo_subset_Icc_self ht))
      _ = P^Cs * (∫ t in (0:ℝ)..1, ∑ i, |deriv (q i) t|) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hP.le _)

theorem variation_power_budget (K m : ℕ) (P Cs Cw : ℝ) (hP : 2 ≤ P) :
    2*(K:ℝ)*(m:ℝ)*P^Cw ≤ P^((2*K*m:ℕ)+max Cw 0) ∧
      P^Cs*(2*(K:ℝ)*(m:ℝ)*P^Cw) ≤
        P^((2*K*m:ℕ)+max Cs 0+max Cw 0) := by
  have hpos : 0 < P := by linarith
  have hnat (n : ℕ) : (n:ℝ)+1 ≤ P^(n:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ,Real.rpow_add hpos,Real.rpow_one]
      have hh := mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hpos.le (n:ℝ))
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hn : 2*(K:ℝ)*(m:ℝ) ≤ P^((2*K*m:ℕ):ℝ) := by
    have hh := hnat (2*K*m)
    have hh' : ((2*K*m:ℕ):ℝ) ≤ P^((2*K*m:ℕ):ℝ) := by linarith
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh'
  have hw : P^Cw ≤ P^(max Cw 0) := Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hs : P^Cs ≤ P^(max Cs 0) := Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hv : 2*(K:ℝ)*(m:ℝ)*P^Cw ≤ P^((2*K*m:ℕ)+max Cw 0) := by
    rw [Real.rpow_add hpos]
    exact mul_le_mul hn hw (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _)
  refine ⟨hv,?_⟩
  calc
    _ ≤ P^(max Cs 0)*P^((2*K*m:ℕ)+max Cw 0) :=
      mul_le_mul hs hv (by positivity) (Real.rpow_nonneg hpos.le _)
    _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring

/-- Complete quantitative fixed-d path stage. All graph-format, cut and power
bounds are uniform before coefficients, seed, scales, levels and endpoints. -/
theorem actual_fixed_d_variation_integral_stage
    (hCell : PublishedSemialgebraicCellDecomposition)
    (hPath : PublishedSemialgebraicPathConnectedness)
    (hHardt : PublishedCompatibleSemialgebraicHardtTriviality)
    (hQE : PublishedRealSemialgebraicity)
    (hNash : PublishedOneVariableNashRegularity)
    (hPiece : PublishedPiecewiseNashExtensions) (k s D : ℕ) :
    ∃ sPath dPath K N : ℕ, ∀ (P Cs Cw : ℝ) (S0 : AugmentedState k)
      (A : Finset (MvPolynomial (Fin 6) ℝ)) (E : Set (Fin 6 → ℝ)),
      2 ≤ P → A.card ≤ s → (∀ p ∈ A, p.totalDegree ≤ D) → PolynomialSignDetermined A E →
      (∀ x ∈ E, augmentedStateNorm (augmentedPullback S0 x) ≤ P^Cw) →
      (∀ x ∈ E, P^(-Cs) ≤ descendingSingularValues
        (dComplement (augmentedPullback S0 x)) (Fin.last 4)) →
      ∀ (d0 : ℝ) (z a b : Fin 6 → ℝ),
        a ∈ connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z →
        b ∈ connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z →
      ∃ γ : SemialgebraicUnitPath (connectedComponentIn {g | g ∈ E ∧ g 3 = d0} z) a b,
      ∃ G : Finset (MvPolynomial (Unit ⊕ Fin 6) ℝ),
        G.card ≤ sPath ∧ (∀ p ∈ G, p.totalDegree ≤ dPath) ∧
        PolynomialSignDetermined G (unitPathGraph γ.toFun) ∧
      ∃ C : Finset ℝ, 0 ∈ C ∧ 1 ∈ C ∧ (∀ c ∈ C, c ∈ Icc (0:ℝ) 1) ∧ C.card ≤ K ∧
        (∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
          (∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => γ.toFun t i) (Ioo u v) ∧
            DerivativeSignOn (fun t => γ.toFun t i) (Ioo u v)) ∧
          (∀ i : AugmentedCoordinateIndex k,
            AnalyticOnNhd ℝ (fun t => augmentedStateCoordinates k
              (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v) ∧
            DerivativeSignOn (fun t => augmentedStateCoordinates k
              (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v))) ∧
        (let q := fun (i : AugmentedCoordinateIndex k) t =>
           augmentedStateCoordinates k (augmentedPullback S0 (γ.toFun t)) i
         let β := fun t => originalAffineBodyCoordinates (γ.toFun t) (deriv γ.toFun t)
         (∀ i, BoundedVariationOn (q i) (Icc (0:ℝ) 1)) ∧
           (∑ i, variationOnFromTo (q i) univ 0 1) ≤ P^((N:ℝ)+max Cw 0) ∧
           (∀ (n : ℕ) (t : ℕ → ℝ), MonotoneOn t (Icc 0 n) →
             (∀ j ∈ Icc 0 n, t j ∈ Icc (0:ℝ) 1) →
             (∑ j ∈ Finset.range n, coordinateL2Norm (fun i => q i (t (j+1))-q i (t j))) ≤
               P^((N:ℝ)+max Cw 0)) ∧
           IntervalIntegrable (fun t => ∑ i, |deriv (q i) t|) volume 0 1 ∧
           (∫ t in (0:ℝ)..1, ∑ i, |deriv (q i) t|) ≤ P^((N:ℝ)+max Cw 0) ∧
           IntervalIntegrable (fun t => coordinateL2Norm (β t)) volume 0 1 ∧
           (∫ t in (0:ℝ)..1, coordinateL2Norm (β t)) ≤ P^((N:ℝ)+max Cs 0+max Cw 0)) := by
  classical
  obtain ⟨sComp,dComp,hComp⟩ := published_bounded_sign_format_component_sign_format
    hCell hHardt hQE (Fin 6) (s+1) (max D 1)
  obtain ⟨sPath,dPath,hPaths⟩ := published_bounded_sign_format_paths
    hPath hHardt hQE (Fin 6) sComp dComp
  obtain ⟨K,hCuts⟩ := published_originalHaar_polynomial_path_cuts
    hCell.toFiniteConnectedCover hHardt hQE hNash hPiece
    (Fin 6) (Fin 6 ⊕ AugmentedCoordinateIndex k) sComp dComp sPath dPath (max k 1)
  refine ⟨sPath,dPath,K,2*K*Fintype.card (AugmentedCoordinateIndex k),?_⟩
  intro P Cs Cw S0 A E hP hAc hAd hAE hwindow hpivot d0 z a b ha hb
  obtain ⟨B,hBc,hBd,hBE⟩ := FixedDFiberComponents.actual_d_fiber_sign_format A E s D hAc hAd hAE d0
  obtain ⟨AComp,hCompc,hCompd,hCompE⟩ := hComp B _ hBc hBd hBE
  obtain ⟨γ,G,hGc,hGd,hG⟩ := hPaths AComp _ hCompc hCompd (hCompE z)
    isPreconnected_connectedComponentIn a ha b hb
  let Q : Fin 6 ⊕ AugmentedCoordinateIndex k → MvPolynomial (Fin 6) ℝ :=
    Sum.elim MvPolynomial.X (SectionIntegralReadouts.augmentedPolynomial S0)
  have hQ : ∀ i, (Q i).totalDegree ≤ max k 1 := by
    intro i
    cases i with
    | inl i => exact (by simp [Q] : (Q (Sum.inl i)).totalDegree ≤ 1).trans (Nat.le_max_right _ _)
    | inr i => exact SectionIntegralReadouts.augmentedPolynomial_degree S0 i
  obtain ⟨C,hC0,hC1,hCI,hCK,hCP⟩ :=
    hCuts _ AComp hCompc hCompd (hCompE z) a b γ G hGc hGd hG Q hQ
  have hp : ∀ u ∈ C, ∀ v ∈ C, u < v → (∀ c ∈ C, c ∉ Ioo u v) →
      (∀ i : Fin 6, AnalyticOnNhd ℝ (fun t => γ.toFun t i) (Ioo u v) ∧
        DerivativeSignOn (fun t => γ.toFun t i) (Ioo u v)) ∧
      (∀ i : AugmentedCoordinateIndex k,
        AnalyticOnNhd ℝ (fun t => augmentedStateCoordinates k
          (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v) ∧
        DerivativeSignOn (fun t => augmentedStateCoordinates k
          (augmentedPullback S0 (γ.toFun t)) i) (Ioo u v)) := by
    intro u hu v hv huv hno
    constructor
    · intro i
      simpa only [Q,Sum.elim_inl,MvPolynomial.eval_X] using hCP u hu v hv huv hno (.inl i)
    · intro i
      simpa only [Q,Sum.elim_inr,SectionIntegralReadouts.augmentedPolynomial_eval] using
        hCP u hu v hv huv hno (.inr i)
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : γ.toFun t ∈ E ∧ γ.toFun t 3 = d0 :=
    connectedComponentIn_subset _ z (γ.mapsTo ht)
  obtain ⟨hbv,hvar,hqi,hqbound,hbi,hbbound⟩ := actual_path_bounds S0 γ.toFun C K d0 P Cs Cw
    (by linarith) hC0 hC1 hCI hCK γ.continuousOn
    (fun t ht => (hmem t ht).2) (fun t ht => hwindow _ (hmem t ht).1)
    (fun t ht => hpivot _ (hmem t ht).1) hp
  have hpow := variation_power_budget K (Fintype.card (AugmentedCoordinateIndex k)) P Cs Cw hP
  refine ⟨γ,G,hGc,hGd,hG,C,hC0,hC1,hCI,hCK,hp,hbv,hvar.trans hpow.1,?_,
    hqi,hqbound.trans hpow.1,hbi,hbbound.trans hpow.2⟩
  intro n t ht hr
  exact (euclidean_partition_le_variation _ 0 1 (by norm_num) hbv n t ht hr).trans
    (hvar.trans hpow.1)

end PaperI.FixedDVariationStage
