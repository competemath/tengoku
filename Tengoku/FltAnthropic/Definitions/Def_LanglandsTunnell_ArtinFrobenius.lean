import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.RingTheory.Frobenius
import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas
import Tengoku.Seed.LinearAlgebra.FreeModule.IdealQuotient
import Tengoku.Seed.FieldTheory.Galois.IsGaloisGroup
import Tengoku.FltAnthropic.Definitions.Def_NarrowRayClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.algebraMap_ringOfIntegers_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.exists_prime_over` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.primeAbove` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.primeAbove_isMaximal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.under_primeAbove` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.primeAbove_liesOver` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.ne_bot_of_under_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.primeAbove_ne_bot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.primeAbove_finite` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.finite_quotient_of_under_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.artinFrob` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.artinSymbol` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LanglandsTunnell.P2.Artin.artinSymbol_prime` (it only prints; the queue checks the axioms of every declaration). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain
open Deep.NTSupply
open scoped nonZeroDivisors

section Frob

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/--
@isnad1 id=isgalois.0h2v.s7.ca0d33e62f43 from=translated src=- shape=d7fc8b72 vocab=eaa99d95
-/
instance isGaloisGroup_ringOfIntegers [IsGalois K M] : IsGaloisGroup (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) :=
  IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) (𝓞 K) (𝓞 M) K M

omit [NumberField K] [NumberField M] in
/--
@isnad1 id=injectiv.0h2v.s7.35363df1e66f from=translated src=- shape=2859a903 vocab=72293ae7
-/
theorem algebraMap_ringOfIntegers_injective : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := by
  intro x y h
  have h' : algebraMap (𝓞 K) M x = algebraMap (𝓞 K) M y := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M, h]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K M, IsScalarTower.algebraMap_apply (𝓞 K) K M] at h'
  exact RingOfIntegers.coe_injective ((algebraMap K M).injective h')

omit [NumberField M] in
/--
@isnad1 id=ex.0h3v.s7.c2ced8eec840 from=translated src=- shape=2c3e7e58 vocab=eb945040
-/
theorem exists_prime_over (v : HeightOneSpectrum (𝓞 K)) : ∃ Q : Ideal (𝓞 M), Q.IsMaximal ∧ Q.under (𝓞 K) = v.asIdeal := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap_ringOfIntegers_injective K M)]; exact bot_le)
  exact ⟨Q, hQ, hQv⟩

def primeAbove (v : HeightOneSpectrum (𝓞 K)) : Ideal (𝓞 M) := (exists_prime_over K M v).choose

variable (v : HeightOneSpectrum (𝓞 K))

/--
@isnad1 id=ismaxima.0h3v.s5.2c9dc369ae10 from=translated src=- shape=a2cdf17e vocab=f0526747
-/
instance primeAbove_isMaximal : (primeAbove K M v).IsMaximal := (exists_prime_over K M v).choose_spec.1

omit [NumberField M] in
/--
@isnad1 id=eq.0h3v.s6.34e1f58c7d78 from=translated src=- shape=7a967cf5 vocab=7445ffcd
-/
theorem under_primeAbove : (primeAbove K M v).under (𝓞 K) = v.asIdeal := (exists_prime_over K M v).choose_spec.2

/--
@isnad1 id=liesover.0h3v.s6.631a31de9688 from=translated src=- shape=f05c2db4 vocab=7b15a4cf
-/
instance primeAbove_liesOver : (primeAbove K M v).LiesOver v.asIdeal := ⟨(under_primeAbove K M v).symm⟩

omit [NumberField K] [NumberField M] in
/--
@isnad1 id=ne.1h4v.s7.b4063784447c from=translated src=- shape=148fd873 vocab=c1e99c18
-/
theorem ne_bot_of_under_eq {Q : Ideal (𝓞 M)} (hQ : Q.under (𝓞 K) = v.asIdeal) : Q ≠ ⊥ := fun h => by
  rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _ (algebraMap_ringOfIntegers_injective K M)] at hQ
  exact v.ne_bot hQ.symm

omit [NumberField M] in
/--
@isnad1 id=ne.0h3v.s6.86191b2aff78 from=translated src=- shape=d6708303 vocab=dea9694e
-/
theorem primeAbove_ne_bot : primeAbove K M v ≠ ⊥ := ne_bot_of_under_eq K M v (under_primeAbove K M v)

/--
@isnad1 id=finite.0h3v.s6.7d3db240bc10 from=translated src=- shape=16f26368 vocab=62fc6e42
-/
instance primeAbove_finite : Finite (𝓞 M ⧸ primeAbove K M v) := Ideal.finiteQuotientOfFreeOfNeBot _ (primeAbove_ne_bot K M v)

omit [NumberField K] in
/--
@isnad1 id=finite.1h4v.s7.6587b8b30e11 from=translated src=- shape=703a4119 vocab=ada99577
-/
theorem finite_quotient_of_under_eq {Q : Ideal (𝓞 M)} (hQ : Q.under (𝓞 K) = v.asIdeal) : Finite (𝓞 M ⧸ Q) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (ne_bot_of_under_eq K M v hQ)

end Frob

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

def artinFrob : M ≃ₐ[K] M := arithFrobAt (𝓞 K) (M ≃ₐ[K] M) (primeAbove K M v)

/--
@isnad1 id=isarithf.0h3v.s7.00ec1d7389a5 from=translated src=- shape=8d0de5fe vocab=baf6e04c
-/
theorem isArithFrobAt_artinFrob : IsArithFrobAt (𝓞 K) (artinFrob K M v) (primeAbove K M v) :=
  IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) (primeAbove K M v)

end Artin

section Symbol

open Deep.NTSupply
open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

def artinSymbol (𝔣 : Ideal (𝓞 K)) : ↥(coprimeToModulus K 𝔣) →* (M ≃ₐ[K] M) := raySymbolHom K 𝔣 (artinFrob K M)

/--
@isnad1 id=eq.1h4v.s14.dffe508b6a99 from=translated src=- shape=cd1bdf4f vocab=a815078e
-/
theorem artinSymbol_prime {𝔣 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinSymbol K M 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ = artinFrob K M v :=
  raySymbolHom_prime K 𝔣 (artinFrob K M) hv

end Symbol

end LanglandsTunnell.P2.Artin

end
