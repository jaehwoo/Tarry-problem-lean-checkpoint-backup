import Revision.Widths
import Revision.CenteredFlux

open Set MeasureTheory
noncomputable section

namespace PaperI.CollarRevision
open BoundedCharacteristic ShortProjectionCaps ParabolicCollar CommonNullAssignment CorridorBands PaperII.EndpointRangesWhole

/-- Bridge data for the original-label input of revised_centered_flux, for
both width alternatives of Lemma 3.17. No comparison with the uninflated L
is imposed on a wide horizontal bridge. -/
theorem signed_width_inputs {ι : Type} [DecidableEq ι] {a b w τ m P δ M : ℝ}
    {cut width rate comp Cf : ℕ} {Γ : ℝ → ℝ} {c d v : Plane → ℝ} {E A : Set Plane}
    {frame : Plane → Fin 6 → ℝ} (labels : Finset ι) (rep : ι → Plane) (fixed : ι → Fin 6 → ℝ)
    (hP : 2≤P) (hτ : 1≤τ) (hH : τ≤b-a) (hm : 1≤m) (hCut : m≤P^cut*τ) (hw : 0≤w) (hδ : δ≤1)
    (hi : IntervalIntegrable (transverseResidual Γ d) volume a b)
    (hWidth : (w≤P^width*m ∧ ∀ z∈Ioo a b,1≤|transverseResidual Γ d z|) ∨
      (∃ C : ℝ,1≤C ∧ ∀ z∈Ioo a b, max 2 (C*w/m) ≤ |transverseResidual Γ d z|))
    (box : ∀ q∈A, CertifiedBox P δ M rate Cf E d v frame q)
    (hRep : ∀ i∈labels, (rep i).2∈Ioo a b ∧ |Γ (rep i).2-(rep i).1|≤2*w ∧
      ∀ y∈uIcc (rep i).1 (Γ (rep i).2), (y,(rep i).2)∈A)
    (hFixed : ∀ i∈labels, ∀ j, |fixedEndpointFrame (fixed i) c d (rep i) j|≤P^comp) :
    let ell := flux (transverseResidual Γ d) a b
    let L := roundedDyadicScale (max m ell)
    let power := rate+(max cut width+1)+comp
    1≤ell ∧ max m ell≤P^cut*ell ∧
    ∀ i∈labels, (rep i).2∈Ioo a b ∧ |Γ (rep i).2-(rep i).1|≤P^power*L ∧
      |d (Γ (rep i).2,(rep i).2)-d (rep i)|≤P^power*L ∧
      IntrinsicReach E d (rep i) (Γ (rep i).2,(rep i).2) (3*(P^power*L)) ∧
      ∀ j,|fixedEndpointFrame (fixed i) c d (rep i) j|≤P^power := by
  intro ell L power
  have h₁ : 1≤P := by linarith
  have hp (k : ℕ) : 0<P^k := pow_pos (by linarith) _
  have hwid := signed_long_width hτ hH (show 0<m by linarith) (one_le_pow₀ h₁ (n:=cut)) hCut hw hi hWidth
  obtain ⟨hH',hell,_,_,hww⟩ := hwid
  have he : τ≤ell := hH.trans hH'
  have hL : 0<L := zero_lt_one.trans_le (one_le_roundedDyadicScale _)
  let j := max cut width
  have hD : max (P^cut) (P^width) ≤ P^j := max_le (pow_le_pow_right₀ h₁ (le_max_left ..)) (pow_le_pow_right₀ h₁ (le_max_right ..))
  have h2 : 2*(max (P^cut) (P^width)) ≤ P^(j+1) := by
    rw [pow_succ,mul_comm (P^j)]
    exact mul_le_mul hP hD (le_max_of_le_left (hp _).le) (by linarith)
  have hW : 2*w≤P^(j+1)*L := hww.trans (mul_le_mul_of_nonneg_right h2 hL.le)
  have hpw : P^(j+1)≤P^power := pow_le_pow_right₀ h₁ (by dsimp [power,j]; omega)
  refine ⟨hell,max_le (hCut.trans (mul_le_mul_of_nonneg_left he (hp _).le))
    (le_mul_of_one_le_left (by linarith) (one_le_pow₀ h₁)),?_⟩
  intro i hmem
  obtain ⟨hz,hwidth,hSeg⟩ := hRep i hmem
  let Bx (x : ℝ) (hx : x∈uIcc (rep i).1 (Γ (rep i).2)) := box _ (hSeg x hx)
  have hDist := hwidth.trans hW
  obtain ⟨hSlope,hPath⟩ := horizontal_bridge (d:=d) (E:=E) (p:=rep i) hL (hp (j+1)) (hp rate).le hDist
    (fun x hx => (Bx x hx).carrier_subset (Bx x hx).mem_carrier)
    (fun x hx => by
      obtain ⟨hd,_,_,hu,_,_,_⟩ := (Bx x hx).small_rates _ (Bx x hx).mem_carrier
      exact ⟨hd.differentiableAt (by norm_num),hu.trans (mul_le_of_le_one_right (hp _).le hδ)⟩)
  have hBound := mul_le_mul_of_nonneg_right hpw hL.le
  refine ⟨hz,hDist.trans hBound,hSlope.trans ?_,hPath.mono (mul_le_mul_of_nonneg_left hBound (by norm_num)),
    fun k => (hFixed i hmem k).trans (pow_le_pow_right₀ h₁ (by dsimp [power]; omega))⟩
  rw [←mul_assoc,←pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h₁ (by dsimp [power,j]; omega)) hL.le

end PaperI.CollarRevision
