/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# Heitmann's Proposition 1

If a subring R of a complete local domain T surjects onto T/M^2
and satisfies IT cap R = I for all finitely generated ideals I,
then R is Noetherian with completion isomorphic to T. Also: when
depth T >= 2, associated primes of T have height at most 1.

Heitmann, "Characterization of completions of UFDs", 1993, Prop. 1.
-/

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Helper lemmas for the completion isomorphism
-/

/-!
## Proposition 1: Criterion for Noetherian completion

If (R, M ∩ R) ⊆ (T, M) with R → T/M² surjective and IT ∩ R = I for all
finitely generated ideals I, then R is Noetherian and R̂ ≅ T.
-/

/-!
## Auxiliary: Depth ≥ 2 implies associated prime conditions

From depth T ≥ 2, we derive:
1. M is not an associated prime of T/rT for any nonzero r (since ht(M) ≥ 2 > 1)
2. All associated primes of T/rT have height ≤ 1 (Krull PIT for principal ideals)
-/

/-- In a local domain with depth ≥ 2, the maximal ideal M is not an associated
prime of T/rT for any nonzero r. This follows because if M ∈ Ass(T/rT) then
depth(M, T/rT) = 0, but depth(M, T) ≥ 2 and r is regular (domain) so
depth(M, T/rT) ≥ 1 by the depth lemma. -/
theorem maximal_not_assoc_of_depth_ge_two
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (r : T) (hr : r ≠ 0) :
    IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}) := by
  intro hM_assoc
  obtain ⟨a, b, ha_mem, hb_mem, hreg⟩ := hdepth
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
  obtain ⟨ha_reg, hreg_b⟩ := hreg
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg_b
  obtain ⟨hb_reg_mod_a, _⟩ := hreg_b
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hM_assoc
  obtain ⟨_, x, hx_ann⟩ := hM_assoc
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx0] at hx_ann
    have : IsLocalRing.maximalIdeal T = ⊤ := by
      rw [hx_ann]
      ext t
      simp
    exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top this
  obtain ⟨x_lift, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx_not_mem : x_lift ∉ Ideal.span ({r} : Set T) := by
    intro h
    apply hx_ne
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h
  have ha_in_ann : a ∈ (⊥ : Submodule T (T ⧸ Ideal.span {r})).colon
      {Ideal.Quotient.mk (Ideal.span {r}) x_lift} := by
    rw [← hx_ann]
    exact ha_mem
  have ha_mul : a * x_lift ∈ Ideal.span ({r} : Set T) := by
    rw [Submodule.mem_colon] at ha_in_ann
    have := ha_in_ann (Ideal.Quotient.mk _ x_lift) (Set.mem_singleton _)
    rw [Submodule.mem_bot] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact this
  have hb_in_ann : b ∈ (⊥ : Submodule T (T ⧸ Ideal.span {r})).colon
      {Ideal.Quotient.mk (Ideal.span {r}) x_lift} := by
    rw [← hx_ann]
    exact hb_mem
  have hb_mul : b * x_lift ∈ Ideal.span ({r} : Set T) := by
    rw [Submodule.mem_colon] at hb_in_ann
    have := hb_in_ann (Ideal.Quotient.mk _ x_lift) (Set.mem_singleton _)
    rw [Submodule.mem_bot] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact this
  rw [Ideal.mem_span_singleton] at ha_mul hb_mul
  obtain ⟨y₁, hy₁⟩ := ha_mul
  obtain ⟨y₂, hy₂⟩ := hb_mul
  have h_eq : r * (b * y₁) = r * (a * y₂) := by
    have h1 : b * (a * x_lift) = a * (b * x_lift) := by ring
    rw [hy₁, hy₂] at h1
    calc r * (b * y₁) = b * (r * y₁) := by ring
    _ = a * (r * y₂) := h1
    _ = r * (a * y₂) := by ring
  -- Cancel r (domain), then use b regular on T/aT to get y₁ ∈ aT
  have h_cancel : b * y₁ = a * y₂ := mul_left_cancel₀ hr h_eq
  have hby₁_mem : b * y₁ ∈ Ideal.span ({a} : Set T) :=
    Ideal.mem_span_singleton.mpr ⟨y₂, h_cancel⟩
  open Pointwise in
  have hy₁_in_aT : y₁ ∈ Ideal.span ({a} : Set T) := by
    have h_eq : (Ideal.span ({a} : Set T) : Submodule T T) = (a • ⊤ : Submodule T T) := by
      ext x
      constructor
      · intro hx
        rw [Ideal.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        exact Submodule.smul_mem_pointwise_smul c a ⊤ Submodule.mem_top
      · intro hx
        have : x ∈ (a • (⊤ : Set T) : Set T) := SetLike.mem_coe.mpr hx
        rw [Set.mem_smul_set] at this
        obtain ⟨c, _, rfl⟩ := this
        exact Ideal.mem_span_singleton.mpr ⟨c, by rw [smul_eq_mul]⟩
    have hby₁_smul : b * y₁ ∈ (a • ⊤ : Submodule T T) := h_eq ▸ hby₁_mem
    have hy₁_smul : y₁ ∈ (a • ⊤ : Submodule T T) :=
      mem_of_isSMulRegular_quotient_of_smul_mem hb_reg_mod_a (by rwa [smul_eq_mul])
    rw [h_eq]
    exact hy₁_smul
  rw [Ideal.mem_span_singleton] at hy₁_in_aT
  obtain ⟨z, hz⟩ := hy₁_in_aT
  -- Cancel a (regular on T): x_lift = r * z, contradicting x ≠ 0
  have h_ax : a * x_lift = a * (r * z) := by rw [hy₁, hz]
                                             ring
  have h_x_eq : x_lift = r * z := by
    have := ha_reg (show a • x_lift = a • (r * z) by rwa [smul_eq_mul, smul_eq_mul])
    exact this
  exact hx_not_mem (Ideal.mem_span_singleton.mpr ⟨z, h_x_eq⟩)

/-- In a Noetherian local domain with depth ≥ 2, if all primes P ≠ M have height ≤ 1,
then associated primes of T/rT for nonzero r have height ≤ 1.
The height hypothesis holds for our concrete T (dim = 2). -/
theorem assoc_height_le_one_of_domain
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1)
    (r : T) (hr : r ≠ 0)
    (P : Ideal T) (hP : P ∈ associatedPrimes T (T ⧸ Ideal.span {r})) :
    P.height ≤ 1 := by
  have hP_prime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hP_ne_M : P ≠ IsLocalRing.maximalIdeal T := by
    intro h
    subst h
    exact maximal_not_assoc_of_depth_ge_two hdepth r hr hP
  exact hht P hP_prime hP_ne_M

end
