/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField
import Tengoku.Seed.NumberTheory.NumberField.Ideal.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Power-residue symbols at prime ideals and integral ideals

Let `K` contain the `n`-th roots of unity and let `P` be a prime ideal
whose absolute norm is coprime to `n`.  Reduction identifies
`μₙ(𝓞 K)` with `μₙ(𝓞 K / P)`.  Pulling the finite-field symbol back along
this identification gives `(a/P)`.

For a nonzero integral ideal `I`, `(a/I)` is the finite product of
`(a/P)` raised to the multiplicity of `P` in `I`.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

attribute [local instance] Ideal.Quotient.field

variable (K : Type*) [Field K] [NumberField K]

noncomputable local instance primeIdealResidueFintype
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ P.asIdeal) :=
  Fintype.ofFinite _

/-- Reduction of `n`-th roots of unity modulo an integral prime ideal.-/
def rootsOfUnityReduction
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rootsOfUnity n (𝓞 K) →*
      rootsOfUnity n (𝓞 K ⧸ P.asIdeal) where
  toFun z :=
    ⟨Ideal.rootsOfUnityMapQuot P.asIdeal n z, by
      change Ideal.rootsOfUnityMapQuot P.asIdeal n (z ^ n) = 1
      rw [show z ^ n = 1 by exact Subtype.ext z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Ideal.rootsOfUnityMapQuot P.asIdeal n)
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul (Ideal.rootsOfUnityMapQuot P.asIdeal n) z w

/-- Reduction on `μₙ` is injective away from `n`.
@isnad1 id=injectiv.1h3v.s14.f822f7481458 from=translated src=- shape=c8db94e9 vocab=1715c7e2
-/
theorem rootsOfUnityReduction_injective
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    Function.Injective (rootsOfUnityReduction K P (n : ℕ)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro z w hzw
  exact
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
      (congrArg Subtype.val hzw)

/-- If `K` contains `μₙ`, then `n` divides `N(P)-1` at every prime
`P ∤ n`.
@isnad1 id=dvd.2h3v.s8.4ae197fc2704 from=translated src=- shape=6988c16a vocab=518d335a
-/
theorem dvd_absNorm_sub_one_of_primitiveRoots
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    (n : ℕ) ∣ Ideal.absNorm P.asIdeal - 1 := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzetaK : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hcard :
      Nat.card (rootsOfUnity (n : ℕ) (𝓞 K)) = (n : ℕ) :=
    hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have hinjective :
      Function.Injective
        (Ideal.rootsOfUnityMapQuot P.asIdeal (n : ℕ)) :=
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
  have hdvd :=
    Subgroup.card_dvd_of_injective
      (Ideal.rootsOfUnityMapQuot P.asIdeal (n : ℕ)) hinjective
  rw [hcard, Nat.card_units] at hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hdvd

/-- Away from `n`, reduction identifies the global integral `n`-th roots
of unity with the residue-field `n`-th roots of unity.-/
noncomputable def rootsOfUnityReductionEquiv
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    rootsOfUnity (n : ℕ) (𝓞 K) ≃*
      rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : Fintype (rootsOfUnity (n : ℕ) (𝓞 K)) :=
    Fintype.ofFinite _
  let f := rootsOfUnityReduction K P (n : ℕ)
  have hinjective : Function.Injective f :=
    rootsOfUnityReduction_injective K P n hcoprime
  let zeta := Classical.choose hmu
  have hzeta := Classical.choose_spec hmu
  have hzetaK : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hsource :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K)) = (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    exact hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have htarget_le :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) ≤
        (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_rootsOfUnity (𝓞 K ⧸ P.asIdeal) (n : ℕ)
  have hsource_le_target :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K)) ≤
        Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) :=
    Fintype.card_le_of_injective f hinjective
  have htarget :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) =
        (n : ℕ) :=
    Nat.le_antisymm htarget_le (by simpa [hsource] using hsource_le_target)
  exact MulEquiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hinjective, hsource.trans htarget.symm⟩)

/-- The reduction equivalence acts by the canonical reduction homomorphism.
@isnad1 id=eq.2h4v.s14.4c571bda0220 from=translated src=- shape=d3f9271b vocab=40bc272f
-/
@[simp]
theorem rootsOfUnityReductionEquiv_apply
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (zeta : rootsOfUnity (n : ℕ) (𝓞 K)) :
    rootsOfUnityReductionEquiv K P n hmu hcoprime zeta =
      rootsOfUnityReduction K P (n : ℕ) zeta :=
  rfl

/-- The cardinality of the residue field is the absolute norm of the
prime ideal.
@isnad1 id=eq.0h2v.s8.91f3269bab60 from=translated src=- shape=0b05b4e6 vocab=b6ada7ba
-/
theorem card_primeIdealResidueField
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (𝓞 K ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- An algebraic integer prime to `P`, regarded as a unit of the residue
field.-/
def primeIdealResidueUnit
    (P : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    (𝓞 K ⧸ P.asIdeal)ˣ :=
  Units.mk0 (Ideal.Quotient.mk P.asIdeal a)
    (by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact ha)

/--
@isnad1 id=eq.3h4v.s9.9efb267be9f8 from=translated src=- shape=d73c3736 vocab=b6511d7f
-/
@[simp]
theorem primeIdealResidueUnit_mul
    (P : HeightOneSpectrum (𝓞 K))
    (a b : 𝓞 K) (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal)
    (hab : a * b ∉ P.asIdeal) :
    primeIdealResidueUnit K P (a * b) hab =
      primeIdealResidueUnit K P a ha *
        primeIdealResidueUnit K P b hb := by
  apply Units.ext
  rfl

/-- The `n`-th power-residue symbol `(a/P)`, valued in the common group
`μₙ(𝓞 K)`.-/
noncomputable def primeIdealPowerResidueSymbol
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hcoprime
  (rootsOfUnityReductionEquiv K P n hmu hcoprime).symm
    (finiteFieldPowerResidueSymbol
      (𝓞 K ⧸ P.asIdeal) n hn
      (primeIdealResidueUnit K P a ha))

/-- Multiplicity of `P` in the prime factorization of a nonzero integral
ideal.-/
def idealPrimeMultiplicity
    (P : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk P.asIdeal).count (Associates.mk I).factors

/-- The finite set of height-one primes dividing a nonzero denominator ideal.

Naming this set keeps every finite-product presentation on the same subtype,
instead of asking typeclass inference to reconstruct definitionally equal
subtypes from separate predicate expressions.-/
def idealPrimeDivisors (I : Ideal (𝓞 K)) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {P | P.asIdeal ∣ I}

omit [NumberField K] in
/-- Membership in the named prime-divisor set is ordinary ideal divisibility.
@isnad1 id=iff.0h3v.s7.952879c9032b from=translated src=- shape=c9e866d5 vocab=16db8331
-/
@[simp]
theorem mem_idealPrimeDivisors
    (I : Ideal (𝓞 K)) (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ idealPrimeDivisors K I ↔ P.asIdeal ∣ I :=
  Iff.rfl

/-- The prime divisors of a nonzero ideal form a finite set.
@isnad1 id=finite.1h2v.s7.4c90600f841c from=translated src=- shape=13bf6caa vocab=5417c3ff
-/
theorem idealPrimeDivisors_finite
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (idealPrimeDivisors K I).Finite :=
  Ideal.finite_factors hI

/-- **Ideal power residue symbol.**  For `I = ∏ P ^ v_P(I)`, define

`(a/I) = ∏ (a/P) ^ v_P(I)`.

The hypotheses only concern the finitely many primes dividing `I`.-/
noncomputable def idealPowerResidueSymbol
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) := by
  letI : Fintype
      (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  exact
    ∏ P : idealPrimeDivisors K I,
      primeIdealPowerResidueSymbol K P.1 n hmu
          (hcoprime P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) a
          (ha P.1 ((mem_idealPrimeDivisors K I P.1).mp P.2)) ^
        idealPrimeMultiplicity K P.1 I

/-- The prime-by-prime factor of the ideal power-residue symbol, extended
by `1` away from the prime divisors of the denominator.-/
noncomputable def idealPowerResidueFactor
    (I : Ideal (𝓞 K))
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : 𝓞 K)
    (hcoprime :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I →
          (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha :
      ∀ P : HeightOneSpectrum (𝓞 K),
        P.asIdeal ∣ I → a ∉ P.asIdeal)
    (P : HeightOneSpectrum (𝓞 K)) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  if hP : P.asIdeal ∣ I then
    primeIdealPowerResidueSymbol K P n hmu
        (hcoprime P hP) a (ha P hP) ^
      idealPrimeMultiplicity K P I
  else
    1

end PowerResidueSymbols
end AlgebraicNumberTheory
