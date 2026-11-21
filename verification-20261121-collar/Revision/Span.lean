import Revision.CapProjection

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace PaperI.CollarRevision

open BoundedCharacteristic CorridorBands ShortProjectionCaps CommonNullAssignment

private theorem compare_rates {a b : ℝ} {f g u v : ℝ → ℝ}
    (hf : ∀ z∈Ioo a b, HasDerivAt f (u z) z) (hg : ∀ z∈Ioo a b, HasDerivAt g (v z) z)
    (h : ∀ z∈Ioo a b, u z ≤ v z) {x y : ℝ} (hx : x∈Ioo a b) (hy : y∈Ioo a b) (hxy : x≤y) :
    f y-f x ≤ g y-g x := by
  have hd (z : ℝ) (hz : z∈Ioo a b) := (hg z hz).sub (hf z hz)
  have hm : MonotoneOn (fun z => g z-f z) (Ioo a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b)
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => sub_nonneg.mpr (h z (interior_subset hz)))
  have hh := hm hx hy hxy
  dsimp at hh
  linarith

private theorem midpoint_span_estimates {a b : ℝ} {α f J : ℝ → ℝ} (hab : a<b)
    (hI : IntervalIntegrable α volume a b) (hc : ContinuousOn α (Ioo a b))
    (hJ : ∀ z∈Ioo a b, 1/2 ≤ J z ∧ J z ≤ 2)
    (hf : ∀ z∈Ioo a b, HasDerivAt f (J z*α z) z)
    {I : Set ℝ} (hImg : MapsTo f (Ioo a b) I) (hLo : BddBelow I) (hHi : BddAbove I) :
    (∀ x∈Ioo a b, ∀ y∈Ioo a b, |f y-f x| ≤ 2*flux α a b) ∧
    ((∀ z∈Ioo a b, 0≤α z) ∨ (∀ z∈Ioo a b, α z≤0) → flux α a b/2≤horizontalSpan I) := by
  let A := flux α a
  have hA (z : ℝ) (hz : z∈Ioo a b) : HasDerivAt A |α z| z := by
    have hi := hI.abs.mono_set (show uIcc a z ⊆ uIcc a b by
      rw [uIcc_of_le hz.1.le,uIcc_of_le hab.le]; exact Icc_subset_Icc_right hz.2.le)
    exact intervalIntegral.integral_hasDerivAt_right hi (hc.abs.stronglyMeasurableAtFilter isOpen_Ioo z hz)
      (hc.abs.continuousAt (isOpen_Ioo.mem_nhds hz))
  have hAc : ContinuousOn A (Icc a b) := by
    simpa only [←uIcc_of_le hab.le] using intervalIntegral.continuousOn_primitive_interval' hI.abs left_mem_uIcc
  have hAa : A a=0 := by simp [A,flux]
  have hmon : MonotoneOn A (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hAc (f':=fun z => |α z|)
    · intro z hz
      rw [interior_Icc] at hz
      exact (hA z hz).hasDerivWithinAt
    · exact fun z _ => abs_nonneg _
  have hUp (x y : ℝ) (hx : x∈Ioo a b) (hy : y∈Ioo a b) (hxy : x≤y) : |f y-f x| ≤ 2*A b := by
    have hB (z : ℝ) (hz : z∈Ioo a b) : |J z*α z| ≤ 2*|α z| := by
      rw [abs_mul,abs_of_nonneg (by linarith [(hJ z hz).1] : 0≤J z)]
      exact mul_le_mul_of_nonneg_right (hJ z hz).2 (abs_nonneg _)
    have h₂ (z : ℝ) (hz : z∈Ioo a b) := (hA z hz).const_mul 2
    have hpos := compare_rates hf h₂ (fun z hz => (abs_le.mp (hB z hz)).2) hx hy hxy
    have hneg := compare_rates (fun z hz => (hf z hz).neg) h₂ (fun z hz => by linarith [(abs_le.mp (hB z hz)).1]) hx hy hxy
    have h0 := hmon (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1.le
    have h1 := hmon (Ioo_subset_Icc_self hy) (right_mem_Icc.mpr hab.le) hy.2.le
    rw [hAa] at h0
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine ⟨?_,?_⟩
  · intro x hx y hy
    rcases le_total x y with h|h
    · exact hUp x y hx hy h
    · rw [abs_sub_comm]; exact hUp y x hy hx h
  · intro hSign
    have span (x y : ℝ) (hx : x∈Ioo a b) (hy : y∈Ioo a b) :
        f y-f x ≤ horizontalSpan I := sub_le_sub (le_csSup hHi (hImg hy)) (csInf_le hLo (hImg hx))
    have hxy (x : ℝ) (hx : x∈Ioo a b) (y : ℝ) (hy : y∈Ioo a b) :
        A y-A x ≤ 2*horizontalSpan I := by
      rcases le_total y x with h|h
      · have hm := hmon (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx) h
        linarith [span x x hx hx]
      · rcases hSign with pos|neg
        · have h := compare_rates hA (fun z hz => (hf z hz).const_mul 2)
            (fun z hz => by rw [abs_of_nonneg (pos z hz)]; nlinarith only [mul_le_mul_of_nonneg_right (hJ z hz).1 (pos z hz)]) hx hy h
          linarith [span x y hx hy]
        · have h := compare_rates hA (fun z hz => (hf z hz).const_mul (-2))
            (fun z hz => by rw [abs_of_nonpos (neg z hz)]; nlinarith only [mul_le_mul_of_nonpos_right (hJ z hz).1 (neg z hz)]) hx hy h
          linarith [span y x hy hx]
    have hcl : closure (Ioo a b)=Icc a b := closure_Ioo hab.ne
    have hc' : ContinuousOn A (closure (Ioo a b)) := hcl.symm ▸ hAc
    have ha : a∈closure (Ioo a b) := hcl.symm ▸ left_mem_Icc.mpr hab.le
    have hb : b∈closure (Ioo a b) := hcl.symm ▸ right_mem_Icc.mpr hab.le
    have ha' (y : ℝ) (hy : y∈Ioo a b) : A y-A a ≤ 2*horizontalSpan I :=
      le_on_closure (fun x hx => hxy x hx y hy) (continuousOn_const.sub hc') continuousOn_const ha
    have hh := le_on_closure ha' (hc'.sub continuousOn_const) continuousOn_const hb
    rw [hAa,sub_zero] at hh
    change A b/2 ≤ _
    linarith

/-- Horizontal sections may be open and the midpoint need not extend smoothly to the ends. -/
theorem projected_graph_span {a b w : ℝ} {Ω : Set Plane} {p d : Plane → ℝ} {Γ : ℝ → ℝ}
    (hab : a<b) (mid : ∀ z∈Ioo a b, (Γ z,z)∈Ω)
    (sec : ∀ q∈Ω, q.2∈Ioo a b ∧ |q.1-Γ q.2|≤2*w ∧
      ∀ y∈uIcc (Γ q.2) q.1, (y,q.2)∈Ω)
    (hΓ : DifferentiableOn ℝ Γ (Ioo a b)) (hc : ContinuousOn (transverseResidual Γ d) (Ioo a b))
    (hi : IntervalIntegrable (transverseResidual Γ d) volume a b)
    (hJ : ∀ q∈Ω, ∃ J : ℝ, 1/2≤J ∧ J≤2 ∧ HasFDerivWithinAt p (J • horizontalForm d q) Ω q)
    (hLo : BddBelow (p '' Ω)) (hHi : BddAbove (p '' Ω)) :
    horizontalSpan (p '' Ω) ≤ 8*w+2*flux (transverseResidual Γ d) a b ∧
    ((∀ z∈Ioo a b,0≤transverseResidual Γ d z) ∨ (∀ z∈Ioo a b,transverseResidual Γ d z≤0) →
      flux (transverseResidual Γ d) a b/2 ≤ horizontalSpan (p '' Ω) ∧
      flux (transverseResidual Γ d) a b/2 ≤ horizontalSpan ((fun z => p (Γ z,z)) '' Ioo a b)) := by
  classical
  choose J hmin hmax hder using hJ
  let K (z : ℝ) := if h : z∈Ioo a b then J (Γ z,z) (mid z h) else 1
  let f (z : ℝ) := p (Γ z,z)
  have hh (z : ℝ) (hz : z∈Ioo a b) : HasDerivAt f (K z*transverseResidual Γ d z) z := by
    have hd := (hΓ.differentiableAt (isOpen_Ioo.mem_nhds hz)).hasDerivAt
    have hpair := hd.prodMk (hasDerivAt_id z)
    have hh' := (hder _ (mid z hz)).comp_hasDerivWithinAt z (f:=fun u : ℝ => (Γ u,u)) (s:=Ioo a b) hpair.hasDerivWithinAt (fun u hu => mid u hu)
    rw [show K z=J _ (mid z hz) by simp only [K,dif_pos hz]]
    simpa [f,horizontalForm,transverseResidual,Function.comp_def] using hh'.hasDerivAt (isOpen_Ioo.mem_nhds hz)
  have hK (z : ℝ) (hz : z∈Ioo a b) : 1/2≤K z ∧ K z≤2 := by
    simp only [K,dif_pos hz]
    exact ⟨hmin _ _,hmax _ _⟩
  let I := p '' Ω
  obtain ⟨hMid,hSigned⟩ := midpoint_span_estimates hab hi hc hK hh
    (I:=I) (fun z hz => ⟨(Γ z,z),mid z hz,rfl⟩) hLo hHi
  have midSub : f '' Ioo a b ⊆ I := by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨(Γ z,z),mid z hz,rfl⟩
  have hMidSigned := (midpoint_span_estimates hab hi hc hK hh (I:=f '' Ioo a b)
    (fun z hz => ⟨z,hz,rfl⟩) (hLo.mono midSub) (hHi.mono midSub)).2
  have hsec (q : Plane) (hq : q∈Ω) : |p q-f q.2|≤4*w := by
    let A := uIcc (Γ q.2) q.1
    let g (y : ℝ) := p (y,q.2)
    let D (y : ℝ) := if h : y∈A then J (y,q.2) ((sec q hq).2.2 y h) else 1
    have hD (y : ℝ) (hy : y∈A) : HasDerivWithinAt g (D y) A y := by
      have h := (hasDerivAt_id y).prodMk (hasDerivAt_const y q.2)
      have h' := (hder _ ((sec q hq).2.2 y hy)).comp_hasDerivWithinAt y h.hasDerivWithinAt
        (fun u hu => (sec q hq).2.2 u hu)
      simpa [g,D,hy,horizontalForm,Function.comp_def] using h'
    have hBound (y : ℝ) (hy : y∈A) : ‖D y‖≤2 := by
      rw [Real.norm_eq_abs,show D y=J _ ((sec q hq).2.2 y hy) by simp [D,hy]]
      rw [abs_of_nonneg (by linarith [hmin _ ((sec q hq).2.2 y hy)] : 0≤J _ _)]
      exact hmax _ _
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hD hBound (convex_Icc _ _)
      (left_mem_uIcc (a:=Γ q.2) (b:=q.1)) (right_mem_uIcc (a:=Γ q.2) (b:=q.1))
    change |p q-f q.2|≤2*|q.1-Γ q.2| at h
    linarith [(sec q hq).2.1]
  refine ⟨?_,fun hs => ⟨hSigned hs,hMidSigned hs⟩⟩
  have ne : I.Nonempty := ⟨_,⟨_,mid _ (nonempty_Ioo.mpr hab).choose_spec,rfl⟩⟩
  have hdiff (u : ℝ) (hu : u∈I) (v : ℝ) (hv : v∈I) : u-v≤8*w+2*flux (transverseResidual Γ d) a b := by
    obtain ⟨x,hx,rfl⟩ := hu
    obtain ⟨y,hy,rfl⟩ := hv
    have h := hMid y.2 (sec y hy).1 x.2 (sec x hx).1
    linarith [(abs_le.mp (hsec x hx)).2,(abs_le.mp h).2,(abs_le.mp (hsec y hy)).1]
  change sSup I-sInf I≤_
  apply sub_le_iff_le_add.mpr
  apply csSup_le ne
  intro u hu
  have hh' : u-(8*w+2*flux (transverseResidual Γ d) a b) ≤ sInf I :=
    le_csInf ne (fun v hv => by linarith [hdiff u hu v hv])
  linarith

end PaperI.CollarRevision
