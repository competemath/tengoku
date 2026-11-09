/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
import Tengoku.Seed.Algebra.BigOperators.Finsupp.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Prime factorization of nonzero fractional ideals

Mathlib's `FractionalIdeal.count` and unique-factorization theorems identify
the multiplicative group of nonzero fractional ideals with the finitely
supported integer exponents of finite primes. This equivalence is formulated
entirely in Mathlib and public Definitions vocabulary.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

namespace NumberFieldFractionalIdealGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The integer exponent of one finite prime, viewed multiplicatively.-/
def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* NumberFieldFractionalIdealGroup K :=
  MonoidHom.mk'
    (fun n => finitePrimeFractionalIdeal v ^ n.toAdd)
    (fun m n => by simp only [toAdd_mul, zpow_add])

/-- Reconstruct a nonzero fractional ideal from finitely many prime
exponents.-/
def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      NumberFieldFractionalIdealGroup K :=
  MonoidHom.mk'
    (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    (fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v))

/--
@isnad1 id=eq.0h2v.s10.3b2ba3c34795 from=translated src=- shape=5da17cf7 vocab=b9cb05fb
-/
@[simp]
theorem factorization_val
    (exps : Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : NumberFieldFractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n := by
  classical
  simp [factorization, primePowerHom, finitePrimeFractionalIdeal, Finsupp.prod]

/-- Only finitely many finite primes occur with nonzero exponent in a
nonzero fractional ideal.
@isnad1 id=finite.0h2v.s7.274fdab556c3 from=translated src=- shape=f0a721d9 vocab=c8a7bc83
-/
theorem finite_count_support (I : NumberFieldFractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

/-- The finitely supported prime-exponent vector of a nonzero fractional
ideal.-/
def countVector (I : NumberFieldFractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

/--
@isnad1 id=eq.0h3v.s7.5d50c6054863 from=translated src=- shape=e38e60a6 vocab=e73fb7dc
-/
@[simp]
theorem countVector_apply (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.663c8424855c from=translated src=- shape=fe2bfd58 vocab=8d58d4b4
-/
@[simp]
theorem count_factorization
    (exps : Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd K v exps.toAdd

/--
@isnad1 id=eq.1h3v.s8.b29d45830d60 from=translated src=- shape=1084a9a2 vocab=0bc9a4c9
-/
theorem ext_count {I J : NumberFieldFractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) (h v)

/--
@isnad1 id=injectiv.0h1v.s8.f42657c8b520 from=translated src=- shape=91cb9817 vocab=9df8a8ec
-/
theorem factorization_injective :
    Function.Injective (factorization (K := K)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization a v, ← count_factorization b v, hab]

/--
@isnad1 id=surjecti.0h1v.s8.2ef58ffcff80 from=translated src=- shape=91cb9817 vocab=83158384
-/
theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact countVector_apply I v

/-- Multiplicative prime factorization of nonzero fractional ideals.-/
def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      NumberFieldFractionalIdealGroup K :=
  MulEquiv.ofBijective (factorization (K := K))
    ⟨factorization_injective, factorization_surjective⟩

end NumberFieldFractionalIdealGroup

end ClassFieldTheory
