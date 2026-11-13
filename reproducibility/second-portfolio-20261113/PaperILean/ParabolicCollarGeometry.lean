import PaperILean.ParabolicCollarTrajectory
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Set Filter

noncomputable section

namespace PaperI.ParabolicCollar
open BoundedCharacteristic

abbrev Coordinates := Fin 2 → ℝ

def collarMap (γ : ℝ → Plane) (d v : Plane → ℝ) (x : Coordinates) : Coordinates :=
  ![(γ (x 0)).1 + d (γ (x 0)) * x 1 + v (γ (x 0)) * (x 1)^2 / 2,
    (γ (x 0)).2 + x 1]

def collarPoint (γ : ℝ → Plane) (d v : Plane → ℝ) (x : Coordinates) : Plane :=
  (collarMap γ d v x 0,collarMap γ d v x 1)

def collarJac (A ν D V D' V' t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A+D'*t+V'*t^2/2,D+V*t;ν,1]

def matrixMap (A : Matrix (Fin 2) (Fin 2) ℝ) : Coordinates →L[ℝ] Coordinates :=
  (Matrix.toLin' A).toContinuousLinearMap

theorem matrixMap_det (A : Matrix (Fin 2) (Fin 2) ℝ) : (matrixMap A).det = A.det := by
  change LinearMap.det (Matrix.toLin' A) = _
  rw [← LinearMap.det_toMatrix',← Matrix.toLin'_symm,LinearEquiv.symm_apply_apply]

private theorem matrixMap_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Coordinates) (i : Fin 2) :
    matrixMap A x i = A i 0*x 0+A i 1*x 1 := by
  change (Matrix.toLin' A) x i = _
  rw [Matrix.toLin'_apply]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem hasFDerivAt_collar {γ : ℝ → Plane} {d v : Plane → ℝ} {x : Coordinates}
    {A ν D' V' : ℝ}
    (ha : HasDerivAt (fun s => (γ s).1) A (x 0))
    (hb : HasDerivAt (fun s => (γ s).2) ν (x 0))
    (hd : HasDerivAt (fun s => d (γ s)) D' (x 0))
    (hv : HasDerivAt (fun s => v (γ s)) V' (x 0)) :
    HasFDerivAt (collarMap γ d v)
      (matrixMap (collarJac A ν (d (γ (x 0))) (v (γ (x 0))) D' V' (x 1))) x := by
  let pr (i : Fin 2) : Coordinates →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hpr (i : Fin 2) : HasFDerivAt (fun y : Coordinates => y i) (pr i) x :=
    (pr i).hasFDerivAt
  have hp := (((hv.comp_hasFDerivAt x (hpr 0)).mul ((hpr 1).mul (hpr 1)))).const_mul (1/2)
  have h₁ := ((ha.comp_hasFDerivAt x (hpr 0)).add ((hd.comp_hasFDerivAt x (hpr 0)).mul (hpr 1))).add hp
  have h₂ := (hb.comp_hasFDerivAt x (hpr 0)).add (hpr 1)
  let L := matrixMap (collarJac A ν (d (γ (x 0))) (v (γ (x 0))) D' V' (x 1))
  have hL : ContinuousLinearMap.pi (fun i => (pr i).comp L) = L := by
    ext z i
    rfl
  change HasFDerivAt (collarMap γ d v) L x
  rw [← hL]
  apply (hasFDerivAt_pi (φ := fun i z => collarMap γ d v z i)).mpr
  intro i
  fin_cases i
  · convert h₁ using 1
    · funext z
      simp [collarMap,Function.comp_def]
      ring
    · ext z
      simp [L,matrixMap_apply,collarJac,pr,smul_eq_mul,Function.comp_def]
      ring
  · convert h₂ using 1
    ext z
    simp [L,matrixMap_apply,collarJac,pr,smul_eq_mul]

private theorem seed_derivatives {γ : ℝ → Plane} {d v : Plane → ℝ} {s A ν : ℝ}
    (ha : HasDerivAt (fun s => (γ s).1) A s)
    (hb : HasDerivAt (fun s => (γ s).2) ν s)
    (hunit : A-d (γ s)*ν=1)
    (hd : DifferentiableAt ℝ d (γ s)) (hv : DifferentiableAt ℝ v (γ s))
    (hV : fderiv ℝ d (γ s) (d (γ s),1)=v (γ s)) :
    HasDerivAt (fun s => d (γ s))
      (fderiv ℝ d (γ s) (1,0)+ν*v (γ s)) s ∧
    HasDerivAt (fun s => v (γ s))
      (fderiv ℝ v (γ s) (1,0)+ν*fderiv ℝ v (γ s) (d (γ s),1)) s := by
  have hγ : HasDerivAt γ (A,ν) s := by simpa using ha.prodMk hb
  have hvec : ((A,ν):Plane) = (1,0) + ν • (d (γ s),1) := by
    apply Prod.ext
    · simp [smul_eq_mul]
      linarith
    · simp [smul_eq_mul]
  constructor
  · have h := hd.hasFDerivAt.comp_hasDerivAt s hγ
    rw [hvec,map_add,map_smul,hV,smul_eq_mul] at h
    exact h
  · have h := hv.hasFDerivAt.comp_hasDerivAt s hγ
    rw [hvec,map_add,map_smul,smul_eq_mul] at h
    exact h

theorem collar_differential {γ : ℝ → Plane} {d v : Plane → ℝ} {x : Coordinates}
    {A ν : ℝ} (ha : HasDerivAt (fun s => (γ s).1) A (x 0))
    (hb : HasDerivAt (fun s => (γ s).2) ν (x 0))
    (hunit : A-d (γ (x 0))*ν=1)
    (hd : DifferentiableAt ℝ d (γ (x 0))) (hv : DifferentiableAt ℝ v (γ (x 0)))
    (hV : fderiv ℝ d (γ (x 0)) (d (γ (x 0)),1)=v (γ (x 0))) :
    let p := γ (x 0)
    let u := fderiv ℝ d p (1,0)
    let V' := fderiv ℝ v p (1,0)+ν*fderiv ℝ v p (d p,1)
    let L := matrixMap (collarJac A ν (d p) (v p) (u+ν*v p) V' (x 1))
    HasFDerivAt (collarMap γ d v) L x ∧ L.det=1+u*x 1+V'*(x 1)^2/2 := by
  dsimp only
  obtain ⟨hd',hv'⟩ := seed_derivatives ha hb hunit hd hv hV
  refine ⟨hasFDerivAt_collar ha hb hd' hv',?_⟩
  rw [matrixMap_det,Matrix.det_fin_two]
  simp [collarJac]
  linear_combination hunit

theorem collar_inside_and_slope {P m δ c M : ℝ} (hP : 2≤P) (hm : 1≤m) (hδ : 0≤δ)
    (hc₁ : c≤1) (C : ℕ) (hsmall : (P^C*δ)*m^3 ≤ 1/16)
    {E : Set Plane} (hE : IsOpen E) {d v : Plane → ℝ}
    (hreg : ∀ p∈E, ContDiffAt ℝ 1 d p) (hregv : ∀ p∈E, DifferentiableAt ℝ v p)
    (hV : ∀ p∈E, fderiv ℝ d p (d p,1)=v p)
    (hY : ∀ p∈E, |fderiv ℝ d p (1,0)|≤P^C*δ)
    (hZv : ∀ p∈E, |fderiv ℝ v p (d p,1)|≤P^C*δ)
    (hv : ∀ p∈E, |v p|≤P^C)
    (retained : Plane → Prop) (hretained : ∀ p∈E, retained p)
    (frame : Plane → Fin 6 → ℝ) (Cframe : ℕ)
    (hframe : ∀ p∈E, ∀ q∈E, relativeFrameNorm frame p q ≤ P^Cframe)
    {γ : ℝ → Plane} {x : Coordinates} (hp : γ (x 0) ∈ E)
    (hM : 4*m<M) (hbuf : HasACBuffer E d (γ (x 0)) M) (ht : |x 1| ≤ c*m) :
    collarPoint γ d v x ∈ E ∧ retained (collarPoint γ d v x) ∧
      |d (γ (x 0))+v (γ (x 0))*x 1-d (collarPoint γ d v x)|≤1 := by
  let h := P^C*δ
  let p := γ (x 0)
  let t := x 1
  have hm₀ : 0≤m := by linarith
  have hh : 0≤h := mul_nonneg (pow_nonneg (by linarith) _) hδ
  have htm : |t|≤m := ht.trans (by nlinarith)
  have hm₁ : m≤m^3 := calc
    m = m*1^2 := by ring
    _ ≤ m*m^2 := by gcongr
    _ = m^3 := by ring
  have htiny : h*(2*m)≤Real.log 2 := by
    have h₁ : h*m≤1/16 := (mul_le_mul_of_nonneg_left hm₁ hh).trans hsmall
    have hl : (1:ℝ)/2≤Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2⁻¹ by norm_num)
      rw [Real.log_inv] at h
      norm_num at h
      linarith
    linarith
  have hrate : ∀ p∈E, |fderiv ℝ d p (1,0)|≤h ∧ |fderiv ℝ d p (d p,1)|≤P^C := by
    intro q hq
    rw [hV q hq]
    exact ⟨hY q hq,hv q hq⟩
  have hloc := bounded_time_characteristic_comparison hP hm hδ C E hE d hreg
    retained hretained frame Cframe hframe htiny hrate
  obtain ⟨y,hy₀,hy,hres⟩ := hloc.2 p.1 p.2 M hp hM hbuf
  have htW : t∈window (2*m) := abs_le.mp (htm.trans (by linarith))
  have hdiff : ∀ q∈E, DifferentiableAt ℝ d q := fun q hq => (hreg q hq).differentiableAt (by norm_num)
  obtain ⟨hslope,hpos⟩ := characteristic_taylor hh hdiff hregv hV hZv hy t htW
  have hpt₀ : point y p.2 0=p := by simp [point,hy₀]
  rw [hpt₀] at hslope hpos
  rw [hy₀] at hpos
  let q := point y p.2 t
  let e := (collarPoint γ d v x).1-q.1
  have he : |e|≤h*|t|^3 := by
    have heq : e = -(y t-(p.1+d p*t+v p*t^2/2)) := by
      simp [e,q,p,t,point,collarPoint,collarMap]
    rwa [heq,abs_neg]
  have ht₃ : h*|t|^3≤1/16 := (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg t) htm _) hh).trans hsmall
  have heM : |e|<M-|t| := by linarith [he.trans ht₃]
  obtain ⟨hsegment,hcorr⟩ := horizontal_correction hE heM (hres t htW).1 hdiff hY
  have heq : horizontal q e 1=collarPoint γ d v x := by
    apply Prod.ext
    · simp [horizontal,e]
    · simp [horizontal,q,p,t,point,collarPoint,collarMap]
  have hcE : collarPoint γ d v x ∈ E := heq ▸ hsegment 1 (by simp)
  refine ⟨hcE,hretained _ hcE,?_⟩
  rw [heq] at hcorr
  have hs₂ : h*|t|^2≤1/16 := (mul_le_mul_of_nonneg_left (calc
    |t|^2 ≤ m^2 := pow_le_pow_left₀ (abs_nonneg _) htm _
    _ ≤ m^2*m := by nlinarith [sq_nonneg m]
    _ = m^3 := by ring) hh).trans hsmall
  have hh₁ : h≤1 := by
    have hm₃ : 1≤m^3 := one_le_pow₀ hm
    calc
      h = h*1 := (mul_one h).symm
      _ ≤ h*m^3 := mul_le_mul_of_nonneg_left hm₃ hh
      _ ≤ 1/16 := hsmall
      _ ≤ 1 := by norm_num
  have hc₀ : h*|e|≤1/16 := by
    calc
      h*|e| ≤ 1*|e| := mul_le_mul_of_nonneg_right hh₁ (abs_nonneg _)
      _ ≤ 1/16 := by simpa using he.trans ht₃
  have htri := abs_add ((d p+v p*t)-d q) (d q-d (collarPoint γ d v x))
  calc
    |d (γ (x 0))+v (γ (x 0))*x 1-d (collarPoint γ d v x)| =
      |d p+v p*t-d q+(d q-d (collarPoint γ d v x))| := by
        congr 1
        change d p+v p*t-d _ = _
        ring
    _ ≤ |d p+v p*t-d q| + |d q-d (collarPoint γ d v x)| := htri
    _ = |d q-(d p+v p*t)| + |d (collarPoint γ d v x)-d q| := by
      rw [abs_sub_comm (d p+v p*t),abs_sub_comm (d q) (d (collarPoint γ d v x))]
    _ ≤ 1/16+1/16 := add_le_add (hslope.trans hs₂) (hcorr.trans hc₀)
    _ ≤ 1 := by norm_num

end PaperI.ParabolicCollar
