import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_FontaineHodge
import Tengoku.FltAnthropic.Theorems.Thm_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
import Tengoku.FltAnthropic.Theorems.Thm_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_DieudonneModule_exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero

set_option autoImplicit false

universe u v w

namespace FontaineKerF

open Deformation Deformation.TruncWitt Deformation.DieudonneModule

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Bialgebra k A]
variable {ℛ : Type w} [CommRing ℛ] {π : ℛ →+* A}

structure Inputs (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] (A : Type v) [CommRing A]
    [Bialgebra k A] {ℛ : Type w} [CommRing ℛ] (π : ℛ →+* A) : Prop where
  crit : ∀ (n : ℕ) (a : TruncatedWittVector p n A), a ∈ fontaineKer p n π →
    TruncWitt.verschiebung a ∈ wittHom k p n A → a ∈ wittHom k p n A
  lift : ∀ (n : ℕ) (u : TruncatedWittVector p n A), frobeniusFun u ∈ fontaineKer p n π →
    ∃ b : TruncatedWittVector p (n + 1) A, b ∈ fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u

/--
@isnad1 id=ex.2h7v.s12.a675c0788fc8 from=translated src=- shape=de44c892 vocab=beb141a0
-/
theorem exists_restrict_eq (H : Inputs p k A π) {n : ℕ} (x : wittHom k p n A)
    (hFx : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    ∃ b : wittHom k p (n + 1) A, (b : TruncatedWittVector p (n + 1) A) ∈ fontaineKer p (n + 1) π ∧
      wittHomRestrict k p A (Nat.le_succ n) b = x := by
  obtain ⟨b, hb, hbx⟩ := H.lift n x hFx
  have hVb : TruncWitt.verschiebung b ∈ wittHom k p (n + 1) A := by
    rw [← shift_truncate_succ, hbx]
    exact shift_mem_wittHom x.2
  exact ⟨⟨b, H.crit (n + 1) b hb hVb⟩, hb, Subtype.ext hbx⟩

/--
@isnad1 id=ex.2h7v.s14.445e5107c083 from=translated src=- shape=fbb33f6d vocab=d1aac561
-/
theorem exists_mem_verschiebung_of_eq (H : Inputs p k A π) {n : ℕ} (x : wittHom k p n A)
    (hFx : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    ∃ b : wittHom k p (n + 1) A, of k p A (n + 1) b ∈ fontaineHodge k p π ∧
      wittHomVerschiebung k p (n + 1) A b = wittHomShift k p n A x := by
  obtain ⟨b, hb, hbx⟩ := exists_restrict_eq H x hFx
  exact ⟨b, of_mem_fontaineHodge hb, by rw [← wittHomShift_restrict, hbx]⟩

/--
@isnad1 id=ex.2h6v.s9.e3adc899f1ad from=translated src=- shape=fac611cf vocab=a6b6aba6
-/
theorem exists_mem_verschiebung_eq_of_frobenius_eq_zero [CharP k p] (H : Inputs p k A π)
    {z : DieudonneModule k p A} (hz : frobenius k p A z = 0) :
    ∃ y ∈ fontaineHodge k p π, verschiebung k p A y = z := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [frobenius_of] at hz
  have hFx : wittHomFrobenius k p n A x = 0 := of_injective n (hz.trans (map_zero _).symm)
  have hFx' : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π := by
    rw [← coe_wittHomFrobenius, hFx, ZeroMemClass.coe_zero]
    exact zero_mem _
  obtain ⟨b, hbL, hVb⟩ := exists_mem_verschiebung_of_eq H x hFx'
  exact ⟨of k p A (n + 1) b, hbL, by rw [verschiebung_of, hVb, of_shift]⟩

namespace Inst
open scoped TensorProduct

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]

/--
@isnad1 id=inputs.3h4v.s9.3bfca5310eb5 from=translated src=- shape=9c9c4323 vocab=cb76a167
-/
theorem inputs (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    @Inputs p _ k _ (k ⊗[𝓞] ℛ) inferInstance inferInstance ℛ _
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom where
  crit _ _ ha hVa := mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom p hp hk hker ℛ ha hVa
  lift n u hu :=
    @TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer ℛ _ p _
      (k ⊗[𝓞] ℛ) inferInstance
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom
      (SpecialFibre.reduction_surjective hk) (SpecialFibre.ker_reduction_eq_span hk hker).le n u hu

end Inst

end FontaineKerF

/--
@isnad1 id=ex.4h5v.s13.d93c8e5458f8 from=translated src=- shape=7f3f413d vocab=85da975b
-/
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {z : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)}
    (hz : Deformation.DieudonneModule.frobenius k p (TensorProduct 𝓞 k ℛ) z = 0) :
    ∃ y ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
      Deformation.DieudonneModule.verschiebung k p (TensorProduct 𝓞 k ℛ) y = z :=
  FontaineKerF.exists_mem_verschiebung_eq_of_frobenius_eq_zero (FontaineKerF.Inst.inputs hp hk hker) hz
