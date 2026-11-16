import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq

set_option maxHeartbeats 800000
set_option autoImplicit false
universe u

open IsLocalRing Polynomial

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

namespace HCprime

section Algebra

variable {R : Type*} [CommRing R] {O : Type*} [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]

end Algebra

section Normed

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

end Normed

section Bridge

variable (W)

@[reducible] noncomputable def adicValuedFrac : Valued (FractionRing W) (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal W).adicValued

attribute [local instance] adicValuedFrac

@[reducible] noncomputable def rankOneFrac : (Valued.v : Valuation (FractionRing W) (WithZero (Multiplicative ℤ))).RankOne :=
  @Valuation.IsRankOneDiscrete.rankOne _ _ _ _ Valued.v
    (IsDiscreteValuationRing.isRankOneDiscrete W (FractionRing W)) 2 one_lt_two

attribute [local instance] rankOneFrac

open scoped Valued

end Bridge

section Main

open IsDiscreteValuationRing

attribute [local instance] adicValuedFrac rankOneFrac
open scoped Valued

end Main

end HCprime

end P1Arch

universe v w

namespace P1Arch
namespace EmbSlope

open IsLocalRing IsDiscreteValuationRing Polynomial

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
variable (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal Ô)

section Restrict
include hv

end Restrict

section Main

end Main

end P1Arch.EmbSlope

open IsLocalRing

namespace P1Arch

section PiLength
variable (R : Type u) [Ring R]

end PiLength

section DVR
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

end DVR

end P1Arch

namespace P1Arch
namespace EmbCount

open IsLocalRing IsDiscreteValuationRing Polynomial

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]

/--
@isnad1 id=le.0h4v.s7.7afd325b8d70 from=translated src=- shape=2185def9 vocab=afe1bfbf
-/
theorem card_algHom_le_finrank (T : Type*) [CommRing T] [Algebra Ô T] [Module.Free Ô T] [Module.Finite Ô T]
    (Φ : Finset (T →ₐ[Ô] C)) : Φ.card ≤ Module.finrank Ô T := by
  classical
  letI := Module.Free.ChooseBasisIndex.fintype Ô T
  let b := Module.Free.chooseBasis Ô T

  have hli : LinearIndependent C (fun φ : Φ => fun i => (φ : T →ₐ[Ô] C) (b i)) := by
    have h0 : LinearIndependent C (fun φ : Φ => ((φ : T →ₐ[Ô] C) : T → C)) := by
      have h := (linearIndependent_monoidHom T C).comp (fun φ : Φ => (φ : T →ₐ[Ô] C).toMonoidHom) (by
        intro φ ψ h
        apply Subtype.ext
        apply AlgHom.ext
        intro t
        exact DFunLike.congr_fun h t)
      exact h
    rw [linearIndependent_iff'] at h0 ⊢
    intro s g hg φ hφ
    apply h0 s g _ φ hφ
    ext t
    have hgi : ∀ i, ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) = 0 := fun i => by
      have := congr_fun hg i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have ht : ∀ ψ : T →ₐ[Ô] C, ψ t = ∑ i, algebraMap Ô C (b.repr t i) * ψ (b i) := by
      intro ψ
      conv_lhs => rw [← b.sum_repr t]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Algebra.smul_def]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∑ ψ ∈ s, g ψ * (algebraMap Ô C (b.repr t i) * (ψ : T →ₐ[Ô] C) (b i))
        = algebraMap Ô C (b.repr t i) * ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ψ _ => ?_; ring
    rw [this, hgi i, mul_zero]
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at hcard
  rw [Module.finrank_eq_card_chooseBasisIndex]
  exact hcard

section Kernel

variable {S : Type u} [CommRing S] [Algebra Ô S]

end Kernel

section Count

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)

variable (hv : ∀ a : Ô, v (algebraMap Ô C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal Ô)
variable (hv0 : ∀ a : Ô, v (algebraMap Ô C a) = 0 → a = 0)
include hv hv0

end Count

end P1Arch.EmbCount
