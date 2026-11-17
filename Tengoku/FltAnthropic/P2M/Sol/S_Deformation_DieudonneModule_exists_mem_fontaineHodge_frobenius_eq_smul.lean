import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_FontaineHodge
import Tengoku.FltAnthropic.Theorems.Thm_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
import Tengoku.FltAnthropic.Theorems.Thm_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_DieudonneModule_exists_mem_fontaineHodge_frobenius_eq_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_frobenius_eq_smul

set_option autoImplicit false

universe u v w

namespace FontaineSH1

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
@isnad1 id=ex.2h7v.s12.58b25541e48d from=translated src=- shape=de44c892 vocab=36e219f6
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
@isnad1 id=ex.2h7v.s14.7fc6fa570638 from=translated src=- shape=fbb33f6d vocab=4d81cac1
-/
theorem exists_mem_verschiebung_of_eq (H : Inputs p k A π) {n : ℕ} (x : wittHom k p n A)
    (hFx : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    ∃ b : wittHom k p (n + 1) A, of k p A (n + 1) b ∈ fontaineHodge k p π ∧
      wittHomVerschiebung k p (n + 1) A b = wittHomShift k p n A x := by
  obtain ⟨b, hb, hbx⟩ := exists_restrict_eq H x hFx
  exact ⟨b, of_mem_fontaineHodge hb, by rw [← wittHomShift_restrict, hbx]⟩

/--
@isnad1 id=ex.5h6v.s10.c7cab41090c6 from=translated src=- shape=2ee7373e vocab=a6d02320
-/
theorem exists_mem_frobenius_eq_smul [CharP k p] (H : Inputs p k A π)
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hπs : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {z : DieudonneModule k p A} (hz : frobenius k p A z ∈ fontaineHodge k p π) :
    ∃ y ∈ fontaineHodge k p π, frobenius k p A z = (p : ℤ) • y := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [frobenius_of, of_mem_fontaineHodge_iff hp' hker hπs] at hz
  obtain ⟨b, hbL, hVb⟩ := exists_mem_verschiebung_of_eq H x hz
  refine ⟨of k p A (n + 1) b, hbL, ?_⟩
  rw [← map_zsmul, ← wittHomFrobenius_verschiebung, hVb, ← wittHomShift_frobenius, of_shift,
    frobenius_of]

namespace Inst
open scoped TensorProduct

/--
@isnad1 id=mem.1h3v.s7.8af6623e8026 from=translated src=- shape=17ffab0a vocab=222ad58a
-/
theorem natCast_mem_nonZeroDivisors {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} {ℛ : Type w} [CommRing ℛ]
    [Algebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    (p : ℛ) ∈ nonZeroDivisors ℛ := by
  have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]

/--
@isnad1 id=inputs.3h4v.s9.efe8216985b5 from=translated src=- shape=9c9c4323 vocab=5d44706c
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

end FontaineSH1

/--
@isnad1 id=ex.4h5v.s13.9b23703f4987 from=translated src=- shape=19f60a58 vocab=cec1f45d
-/
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {z : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)}
    (hz : Deformation.DieudonneModule.frobenius k p (TensorProduct 𝓞 k ℛ) z ∈
      Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom) :
    ∃ y ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
      Deformation.DieudonneModule.frobenius k p (TensorProduct 𝓞 k ℛ) z = (p : ℤ) • y :=
  FontaineSH1.exists_mem_frobenius_eq_smul (FontaineSH1.Inst.inputs hp hk hker)
    (FontaineSH1.Inst.natCast_mem_nonZeroDivisors hp) (Deformation.SpecialFibre.reduction_surjective hk)
    (Deformation.SpecialFibre.ker_reduction_eq_span hk hker).le hz
