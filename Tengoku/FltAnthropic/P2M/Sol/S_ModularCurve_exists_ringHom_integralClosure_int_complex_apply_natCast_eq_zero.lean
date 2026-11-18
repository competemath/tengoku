import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero

set_option autoImplicit false

namespace P2mIntegralClosureRedHom

open Polynomial

/--
@isnad1 id=nonempty.1h3v.s6.b7eadbcd8ac6 from=translated src=- shape=672aabd8 vocab=cd52a2ae
-/
theorem nonempty_ringHom_of_charP_of_integral (F : Type*) [Field F] (K : Type*) [Field K]
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP F p] [CharP K p]
    (hint : ∀ x : F, ∃ f : ℤ[X], f.Monic ∧ f.eval₂ (Int.castRingHom F) x = 0) :
    Nonempty (F →+* K) := by
  letI algF : Algebra (ZMod p) F := ZMod.algebra F p
  letI algK : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Algebra.IsIntegral (ZMod p) F := by
    refine ⟨fun x => ?_⟩
    obtain ⟨f, hfm, hf⟩ := hint x
    refine ⟨f.map (Int.castRingHom (ZMod p)), hfm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p)) = Int.castRingHom F :=
      RingHom.ext_int _ _
    rw [hcomp, hf]
  let ψ : F →ₐ[ZMod p] K := IsAlgClosed.lift
  exact ⟨ψ.toRingHom⟩

/--
@isnad1 id=ismaxima.0h1v.s4.83b5da2027c2 from=translated src=- shape=1a4968a7 vocab=592666df
-/
theorem span_natCast_int_isMaximal (p : ℕ) [hp : Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible

/--
@isnad1 id=le.0h1v.s9.0573afabbca6 from=translated src=- shape=7eb17e49 vocab=060e81ab
-/
theorem ker_algebraMap_int_integralClosure_le (I : Ideal ℤ) :
    RingHom.ker (algebraMap ℤ ↥(integralClosure ℤ ℂ)) ≤ I := by
  intro n hn
  rw [RingHom.mem_ker] at hn
  have h1 : ((algebraMap ℤ ↥(integralClosure ℤ ℂ) n : ↥(integralClosure ℤ ℂ)) : ℂ) = 0 := by
    rw [hn]; rfl
  have h3 : ((algebraMap ℤ ↥(integralClosure ℤ ℂ) n : ↥(integralClosure ℤ ℂ)) : ℂ) = (n : ℂ) := by
    simp
  rw [h3] at h1
  have : n = 0 := by exact_mod_cast h1
  subst this
  exact I.zero_mem

/--
@isnad1 id=ex.0h1v.s9.594b93e86431 from=translated src=- shape=58705ca1 vocab=1934e89d
-/
theorem exists_isMaximal_comap_eq (p : ℕ) [Fact p.Prime] :
    ∃ Q : Ideal ↥(integralClosure ℤ ℂ), Q.IsMaximal ∧
      Q.comap (algebraMap ℤ ↥(integralClosure ℤ ℂ)) = Ideal.span {(p : ℤ)} := by
  haveI := span_natCast_int_isMaximal p
  exact Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥(integralClosure ℤ ℂ))
    (Ideal.span {(p : ℤ)}) (ker_algebraMap_int_integralClosure_le _)

/--
@isnad1 id=nonempty.0h2v.s7.405a095978df from=translated src=- shape=bd41d876 vocab=d0045948
-/
theorem nonempty_ringHom (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    [CharP K p] : Nonempty (↥(integralClosure ℤ ℂ) →+* K) := by
  obtain ⟨Q, hQmax, hQ⟩ := exists_isMaximal_comap_eq p

  letI : Field (↥(integralClosure ℤ ℂ) ⧸ Q) := Ideal.Quotient.field Q

  have hpQ : ((p : ↥(integralClosure ℤ ℂ))) ∈ Q := by
    have h1 : (p : ℤ) ∈ Q.comap (algebraMap ℤ ↥(integralClosure ℤ ℂ)) := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hp0 : ((p : ↥(integralClosure ℤ ℂ) ⧸ Q)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ
  haveI hchar : CharP (↥(integralClosure ℤ ℂ) ⧸ Q) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0

  have hint : ∀ x : ↥(integralClosure ℤ ℂ) ⧸ Q, ∃ f : ℤ[X], f.Monic ∧
      f.eval₂ (Int.castRingHom (↥(integralClosure ℤ ℂ) ⧸ Q)) x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : IsIntegral ℤ y := Algebra.IsIntegral.isIntegral y
    obtain ⟨f, hfm, hf⟩ := hy
    refine ⟨f, hfm, ?_⟩
    have hcomp : Int.castRingHom (↥(integralClosure ℤ ℂ) ⧸ Q)
        = (Ideal.Quotient.mk Q).comp (algebraMap ℤ ↥(integralClosure ℤ ℂ)) :=
      RingHom.ext_int _ _
    rw [hcomp, ← Polynomial.hom_eval₂, hf, map_zero]
  obtain ⟨ψ⟩ := nonempty_ringHom_of_charP_of_integral (↥(integralClosure ℤ ℂ) ⧸ Q) K p hint
  exact ⟨ψ.comp (Ideal.Quotient.mk Q)⟩

end P2mIntegralClosureRedHom

/--
@isnad1 id=ex.0h2v.s10.81a90e8351d2 from=translated src=- shape=3b462c8c vocab=818aea0e
-/
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ φ : ↥(integralClosure ℤ ℂ) →+* K, φ (p : ↥(integralClosure ℤ ℂ)) = 0 := by
  obtain ⟨φ⟩ := P2mIntegralClosureRedHom.nonempty_ringHom K p
  exact ⟨φ, by rw [map_natCast]; exact CharP.cast_eq_zero K p⟩
