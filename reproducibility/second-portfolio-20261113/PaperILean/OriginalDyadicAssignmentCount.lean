import PaperILean.OriginalDyadicCoreAssignment
import PaperILean.OriginalDyadicScaleCount

/-! I1259: logarithmically count the SAME original dyadic/core-component pairs.
No joint path, diameter or prepared-interval choice is asserted here. -/
noncomputable section
namespace PaperI
open Set

theorem originalDyadicComponentAssigned_mem_scaleWindow {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hbuffer : ∀ j, active ω j →
      δ ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ)
    {j : Λ} {k : ℤ} {i : Fin D.count}
    (hj : originalDyadicComponentAssigned D active param radius point ω j k i) :
    k ∈ originalDyadicScaleWindow δ (3*radius ω+1) := by
  let z := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)
  have hc : (WithLp.equiv 2 (Fin 2 → ℝ)) z ∈ planarBoundedCore
      ((WithLp.equiv 2 (Fin 2 → ℝ)) '' E) (radius ω) ((2:ℝ)^k) := by
    simpa only [z,Equiv.apply_symm_apply,hE] using hj.1.2
  have hρ := (planarBoundedCore_coordinates_iff hT ho hbox z).mp hc
  exact originalDyadicScaleWindow_mem hδ (hbuffer j hj.1.1)
    (by simpa only [Equiv.symm_apply_apply] using
      planar_infDist_compl_le_of_coordinateBox hT hbox hρ.1) hρ.2

theorem originalDyadicComponentAssigned_box_finite_count {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hbuffer : ∀ j, active ω j →
      δ ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) :
    Finite {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ∧
    Nat.card {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ≤
        (originalDyadicScaleWindow δ (3*radius ω+1)).card * D.count := by
  apply originalDyadicComponentAssigned_finite_count
  intro j k i hj
  exact originalDyadicComponentAssigned_mem_scaleWindow D active param radius point ω
    ho hT hE hbox hδ hbuffer hj

theorem originalDyadicComponentAssigned_box_log_count {Ω Λ ρ : Type*}
    {G : Set ((ρ ⊕ Fin 2) → ℝ)}
    (D : JointComponentPartition (planarBoundedBandFamily G))
    (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
    (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
    {E : Set (WithLp 2 (Fin 2 → ℝ))} (ho : IsOpen E)
    (hT : 0 ≤ radius ω)
    (hE : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω))
    (hbox : (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hbuffer : ∀ j, active ω j →
      δ ≤ Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) :
    Finite {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} ∧
    (Nat.card {q : ℤ × Fin D.count // ∃ j,
      originalDyadicComponentAssigned D active param radius point ω j q.1 q.2} : ℝ) ≤
        max 0 (2+Real.logb 2 ((3*radius ω+1)/δ)) * D.count := by
  obtain ⟨hf,hc⟩ := originalDyadicComponentAssigned_box_finite_count
    D active param radius point ω ho hT hE hbox hδ hbuffer
  refine ⟨hf, (Nat.cast_le.mpr hc).trans ?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (originalDyadicScaleWindow_card_le_max hδ)
    (Nat.cast_nonneg D.count)

universe u v w

/-- The exponent is chosen from the fixed buffer exponent and catalogue bound
before all coefficient families, parameters, labels, P and T. -/
theorem originalDyadicComponentAssigned_uniform_count (q M : ℕ) :
    ∃ n : ℕ, ∀ {Ω : Type u} {Λ : Type v} {ρ : Type w}
      {G : Set ((ρ ⊕ Fin 2) → ℝ)}
      (D : JointComponentPartition (planarBoundedBandFamily G)), D.count ≤ M →
      ∀ (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
        (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
        (E : Set (WithLp 2 (Fin 2 → ℝ))), IsOpen E → 0 ≤ radius ω →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω) →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω) →
        ∀ P : ℝ, 2 ≤ P →
        (∀ j, active ω j → (P^q)⁻¹ ≤
          Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
        Finite {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} ∧
        (Nat.card {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} : ℝ) ≤
            P^n * (1+Real.log (max 1 (radius ω))) := by
  obtain ⟨n,hn⟩ := originalDyadicScaleWindow_polynomial_log_bound q
  obtain ⟨m,hm⟩ := uniform_constant_le_power (M:ℝ)
  refine ⟨n+m,?_⟩
  intro Ω Λ ρ G D hM active param radius point ω E ho hT hE hbox P hP hb
  obtain ⟨hf,hc⟩ := originalDyadicComponentAssigned_box_finite_count
    D active param radius point ω ho hT hE hbox (by positivity : 0 < (P^q)⁻¹) hb
  refine ⟨hf, (Nat.cast_le.mpr hc).trans ?_⟩
  rw [Nat.cast_mul]
  calc
    _ ≤ (P^n*(1+Real.log (max 1 (radius ω)))) * P^m := by
      apply mul_le_mul (hn P (radius ω) hP hT)
        ((Nat.cast_le.mpr hM).trans (hm P hP)) (Nat.cast_nonneg _)
      have hl := Real.log_nonneg (le_max_left (1:ℝ) (radius ω))
      positivity
    _ = _ := by rw [pow_add]; ring

/-- Real buffer exponents are not silently restricted to integers. -/
theorem originalDyadicComponentAssigned_uniform_real_count (c : ℝ) (M : ℕ) :
    ∃ n : ℕ, ∀ {Ω : Type u} {Λ : Type v} {ρ : Type w}
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
            P^n * (1+Real.log (max 1 (radius ω))) := by
  obtain ⟨q,hq⟩ := original_inverse_real_power_minorant c
  obtain ⟨n,hn⟩ := originalDyadicComponentAssigned_uniform_count.{u,v,w} q M
  refine ⟨n,?_⟩
  intro Ω Λ ρ G D hM active param radius point ω E ho hT hE hbox P hP hb
  exact hn D hM active param radius point ω E ho hT hE hbox P hP
    (fun j hj => (hq P hP).trans (hb j hj))

/-- Printed logarithm on the explicitly normalized range; this added range
is a proposed technical repair, not a claim about the unamended lemma. -/
theorem originalDyadicComponentAssigned_manuscript_range_count (c : ℝ) (M : ℕ) :
    ∃ n : ℕ, ∀ {Ω : Type u} {Λ : Type v} {ρ : Type w}
      {G : Set ((ρ ⊕ Fin 2) → ℝ)}
      (D : JointComponentPartition (planarBoundedBandFamily G)), D.count ≤ M →
      ∀ (active : Ω → Λ → Prop) (param : Ω → ρ → ℝ) (radius : Ω → ℝ)
        (point : Ω → Λ → Fin 2 → ℝ) (ω : Ω)
        (E : Set (WithLp 2 (Fin 2 → ℝ))), IsOpen E → 2 ≤ radius ω →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E = projectionFiber G (param ω) →
        (WithLp.equiv 2 (Fin 2 → ℝ)) '' E ⊆ planarCoordinateBox (radius ω) →
        ∀ P : ℝ, 2 ≤ P →
        (∀ j, active ω j → P^(-c) ≤
          Metric.infDist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (point ω j)) Eᶜ) →
        Finite {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} ∧
        (Nat.card {a : ℤ × Fin D.count // ∃ j,
          originalDyadicComponentAssigned D active param radius point ω j a.1 a.2} : ℝ) ≤
            P^n * (1+Real.log (radius ω)) := by
  obtain ⟨n,hn⟩ := originalDyadicComponentAssigned_uniform_real_count.{u,v,w} c M
  refine ⟨n,?_⟩
  intro Ω Λ ρ G D hM active param radius point ω E ho hT hE hbox P hP hb
  simpa only [max_eq_right (by linarith : (1:ℝ) ≤ radius ω)] using
    hn D hM active param radius point ω E ho (by linarith) hE hbox P hP hb

end PaperI
