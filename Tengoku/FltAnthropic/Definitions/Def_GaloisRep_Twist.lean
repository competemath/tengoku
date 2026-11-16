import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_StrictOrdinary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

def _root_.Tengoku.FltAnthropic.GaloisCharIsAdicContinuous (A : Type) [CommRing A] [IsLocalRing A]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ((χ σ : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ n

namespace Tengoku.FltAnthropic.GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

/--
@isnad1 id=galoisch.1h2v.s11.31c85cfc62f7 from=translated src=- shape=1516e607 vocab=0a7beeae
-/
theorem galoisCharIsAdicContinuous_of_finiteLevel
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (h : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → χ σ = 1) :
    GaloisCharIsAdicContinuous A χ := by
  intro n
  obtain ⟨L, hL, hχ⟩ := h
  refine ⟨L, hL, fun σ hσ => ?_⟩
  rw [hχ σ hσ, Units.val_one, sub_self]
  exact Submodule.zero_mem _

@[reducible] noncomputable def twist (ρ : GaloisRepAdic A)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ) : GaloisRepAdic A where
  V := ρ.V
  finrank_eq := ρ.finrank_eq
  ρ := { toFun := fun σ => ((χ σ : Aˣ) : A) • ρ.ρ σ
         map_one' := by rw [map_one, map_one, Units.val_one, one_smul]
         map_mul' := fun σ τ => by
           rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm] }
  isAdicContinuous := by
    intro n
    obtain ⟨L₁, hL₁, h₁⟩ := ρ.isAdicContinuous n
    obtain ⟨L₂, hL₂, h₂⟩ := hχ n
    haveI := hL₁
    haveI := hL₂
    refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ v => ?_⟩
    have hσ₁ : ∀ x ∈ L₁, σ x = x := fun x hx => hσ x ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx)
    have hσ₂ : ∀ x ∈ L₂, σ x = x := fun x hx => hσ x ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx)
    have hsplit : ((χ σ : Aˣ) : A) • ρ.ρ σ v - v =
        ((χ σ : Aˣ) : A) • (ρ.ρ σ v - v) + (((χ σ : Aˣ) : A) - 1) • v := by
      rw [smul_sub, sub_smul, one_smul, sub_add_sub_cancel]
    show ((χ σ : Aˣ) : A) • ρ.ρ σ v - v ∈ _
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h₁ σ hσ₁ v))
      (Submodule.smul_mem_smul (h₂ σ hσ₂) Submodule.mem_top)

variable (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
  (hχ : GaloisCharIsAdicContinuous A χ)

/--
@isnad1 id=eq.1h3v.s8.f4f42047c82a from=translated src=- shape=df83fac0 vocab=df7e2fd9
-/
theorem twist_V : (ρ.twist χ hχ).V = ρ.V := rfl

/--
@isnad1 id=eq.1h4v.s12.ae3b6dbd9885 from=translated src=- shape=e061b57a vocab=c607bef8
-/
theorem twist_ρ_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).ρ σ = ((χ σ : Aˣ) : A) • ρ.ρ σ := rfl

/--
@isnad1 id=eq.1h5v.s12.da055c8ebcab from=translated src=- shape=0d316ac0 vocab=c607bef8
-/
theorem twist_ρ_apply_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    (ρ.twist χ hχ).ρ σ v = ((χ σ : Aˣ) : A) • ρ.ρ σ v := rfl

/--
@isnad1 id=eq.1h4v.s10.7e1090b6191e from=translated src=- shape=7a32f29a vocab=518d127c
-/
theorem trace_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).trace σ = ((χ σ : Aˣ) : A) * ρ.trace σ := by
  show LinearMap.trace A ρ.V (((χ σ : Aˣ) : A) • ρ.ρ σ) = _
  rw [map_smul, smul_eq_mul]
  rfl

/--
@isnad1 id=isunrami.3h4v.s10.a117d2fbc3f5 from=translated src=- shape=65866cbe vocab=492e2e12
-/
theorem isUnramifiedAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnramifiedAt q) : (ρ.twist χ hχ).IsUnramifiedAt q := by
  intro P hP σ hσ
  rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  exact h P hP σ hσ

/--
@isnad1 id=isunipot.3h4v.s10.5e82f08c96bb from=translated src=- shape=65866cbe vocab=83161c0c
-/
theorem isUnipotentOnInertiaAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnipotentOnInertiaAt q) : (ρ.twist χ hχ).IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  have e : (ρ.twist χ hχ).ρ σ = ρ.ρ σ := by
    rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  rw [e]
  exact h P hP σ hσ

/--
@isnad1 id=isstrict.3h4v.s10.aa6873c7f34d from=translated src=- shape=65866cbe vocab=7a30b9db
-/
theorem isStrictOrdinaryAt_twist {p : ℕ}
    (hp : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsStrictOrdinaryAt p) : (ρ.twist χ hχ).IsStrictOrdinaryAt p := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨L, hb, hD, hI, hsc⟩ := h.2 P hP
  refine ⟨L, hb, ?_, ?_, ?_⟩
  · intro σ hσ v hv
    rw [twist_ρ_apply_apply]
    exact L.smul_mem _ (hD σ hσ v hv)
  · intro σ hσ v
    rw [twist_ρ_apply_apply, hp P hP σ hσ, Units.val_one, one_smul]
    exact hI σ hσ v
  · intro σ hσ
    obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
    refine ⟨((χ σ : Aˣ) : A) * x, ((χ σ : Aˣ) : A) * z, ?_, ?_, ?_⟩
    · intro w hw
      rw [twist_ρ_apply_apply, hx w hw, smul_smul]
    · intro v
      have e : (ρ.twist χ hχ).ρ σ v - (((χ σ : Aˣ) : A) * z) • v =
          ((χ σ : Aˣ) : A) • (ρ.ρ σ v - z • v) := by
        rw [twist_ρ_apply_apply, smul_sub, smul_smul]
      rw [e]
      exact L.smul_mem _ (hz v)
    · intro n a ha
      have e : ((χ σ : Aˣ) : A) * x - (a : A) * (((χ σ : Aˣ) : A) * z) =
          ((χ σ : Aˣ) : A) * (x - (a : A) * z) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (hxz n a ha)

end Tengoku.FltAnthropic.GaloisRepAdic
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
