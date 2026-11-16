import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GaloisRep

noncomputable section

/--
@isnad1 id=isprime.0h1v.s4.a55d79ccb0a6 from=translated src=- shape=1a4968a7 vocab=6fb39c7a
-/
instance ratLocalizedAt.span_isPrime (q : ℕ) [Fact q.Prime] : (Ideal.span {(q : ℤ)}).IsPrime := by
  have hq : Prime (q : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : q.Prime)
  exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq

def ratLocalizedAtResidue (q : ℕ) [Fact q.Prime] : ↥(ratLocalizedAt q) →+* ZMod q :=
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (S := ↥(ratLocalizedAt q))
    (g := Int.castRingHom (ZMod q))
    (fun y => by
      refine isUnit_iff_ne_zero.mpr ?_
      simp only [Int.coe_castRingHom, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      exact y.2 (Ideal.mem_span_singleton.mpr (by exact_mod_cast h)))

instance instAlgebraRatLocalizedAtZMod (q : ℕ) [Fact q.Prime] :
    Algebra ↥(ratLocalizedAt q) (ZMod q) :=
  (ratLocalizedAtResidue q).toAlgebra

end

end GaloisRep
