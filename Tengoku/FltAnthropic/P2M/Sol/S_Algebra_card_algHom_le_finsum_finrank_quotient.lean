import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_card_algHom_le_finsum_finrank_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_card_algHom_le_finsum_finrank_quotient.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_card_algHom_le_finsum_finrank_quotient

set_option maxHeartbeats 800000
set_option autoImplicit false
universe u v

open IsLocalRing

namespace DepthFreeEmbCount

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]

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

end Count

end DepthFreeEmbCount
