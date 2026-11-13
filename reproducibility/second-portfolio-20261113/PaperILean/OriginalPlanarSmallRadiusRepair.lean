import PaperILean.OriginalDyadicAssignmentCount
import PaperILean.PlanarRadiusNormalization

/-! Resolves ERROR:planar_log_small_radius_146 for the explicitly corrected
count statement. The SAME originalDyadicComponentAssigned predicate is kept.
No completed full strip assignment or main theorem is asserted.
-/
noncomputable section
namespace PaperI
open Set

theorem planarCoordinateBox_subset_normalized (T : ℝ) :
    planarCoordinateBox T ⊆ planarCoordinateBox (max 2 T) :=
  planarCoordinateBox_mono (le_max_right _ _)

theorem measurable_planarLogSize : Measurable planarLogSize :=
  continuous_planarLogSize.measurable

universe u v w

/-- All nonnegative radii, positive fixed output exponent, unchanged original
assignment. C is chosen from c and M BEFORE every coefficient family, label
type, sample parameter, P and T. Published inputs remain in catalogue creation,
exactly as in checkpoint146; none is newly assumed here. -/
theorem originalDyadicComponentAssigned_repaired_count (c : ℝ) (M : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ {Ω : Type u} {Λ : Type v} {ρ : Type w}
      {G : Set ((ρ ⊕ Fin 2) → ℝ)}
      (D : JointComponentPartition (planarBoundedBandFamily G)), D.count ≤ M →
      ∀ (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
        (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
        (E : Set (WithLp 2 (Fin 2 → ℝ))), IsOpen E → 0 ≤ radius ω →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω) →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω) →
        ∀ P : ℝ, 2 ≤ P →
        (∀ j, active ω j → P^(-c) ≤
          Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
        Finite {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} ∧
        (Nat.card {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} : ℝ) ≤
            P^C * (planarLogSize (radius ω))^C := by
  obtain ⟨n, hn⟩ := originalDyadicComponentAssigned_uniform_real_count.{u,v,w} c M
  refine ⟨n+1, Nat.succ_pos n, ?_⟩
  intro Ω Λ ρ G D hM active param radius point ω E ho hT hE hbox P hP hb
  obtain ⟨hf, hc⟩ := hn D hM active param radius point ω E ho hT hE hbox P hP hb
  exact ⟨hf, hc.trans (planarLogSize_single_exponent (by linarith : 1 ≤ P) n)⟩

/-- The old obstruction range now costs P^C, not zero; the data are unchanged. -/
theorem originalDyadicComponentAssigned_repaired_small_count (c : ℝ) (M : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ {Ω : Type u} {Λ : Type v} {ρ : Type w}
      {G : Set ((ρ ⊕ Fin 2) → ℝ)}
      (D : JointComponentPartition (planarBoundedBandFamily G)), D.count ≤ M →
      ∀ (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
        (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
        (E : Set (WithLp 2 (Fin 2 → ℝ))), IsOpen E → 0 ≤ radius ω → radius ω ≤ 1 →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω) →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω) →
        ∀ P : ℝ, 2 ≤ P →
        (∀ j, active ω j → P^(-c) ≤
          Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
        Finite {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} ∧
        (Nat.card {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} : ℝ) ≤ P^C := by
  obtain ⟨C, hC, h⟩ := originalDyadicComponentAssigned_repaired_count.{u,v,w} c M
  refine ⟨C, hC, ?_⟩
  intro Ω Λ ρ G D hM active param radius point ω E ho hT hT1 hE hbox P hP hb
  simpa only [planarLogSize_eq_one hT1, one_pow, mul_one] using
    h D hM active param radius point ω E ho hT hE hbox P hP hb

end PaperI
