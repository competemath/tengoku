import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_XOneP_algebraMap_smul_eq_of_isCyclotomicExtension_of_charP

set_option autoImplicit false

/--
@isnad1 id=eq.4h7v.s10.c7a09d5c7709 from=translated src=- shape=9d99d76f vocab=c2a71998
-/
theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by
  intro s a

  have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
    have hpk : algebraMap A k (p : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k p
    have hp0 : (p : A) ≠ 0 := by
      intro h
      have h2 : (p : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
      exact (Nat.Prime.ne_zero (Fact.out : p.Prime)) (by exact_mod_cast h2)
    haveI : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
    have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := fun h => hp0 (by
      have : (p : A) ∈ RingHom.ker (algebraMap A k) := hpk
      rw [h] at this; exact this)
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)

  obtain ⟨n, hn⟩ := ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension p L ζ hζ A hAp hζA a

  let es : A ≃+* A := MulSemiringAction.toRingEquiv (L ≃ₐ[ℚ] L) A s
  have hes : ∀ x : A, es x = s • x := fun x => rfl
  have hsm : ∀ m : A, m ∈ IsLocalRing.maximalIdeal A → s • m ∈ IsLocalRing.maximalIdeal A := by
    intro m hm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    intro hu
    apply hm
    have := hu.map es.symm
    rwa [← hes, RingEquiv.symm_apply_apply] at this
  have hsn : s • ((n : ℤ) : A) = (n : A) := by rw [← hes, map_intCast]

  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker]
  have : s • a - a = s • (a - n) - (a - n) := by
    rw [smul_sub, hsn]; ring
  rw [this]
  exact Ideal.sub_mem _ (hsm _ hn) hn
